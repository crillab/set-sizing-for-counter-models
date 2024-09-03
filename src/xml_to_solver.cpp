#include "../include/xml_to_solver.hpp"
#include "utils/clock.hpp"
#include "pugixml.hpp"

#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <vector>

using xml_node = const pugi::xml_node &;

enum typref { POW_INTEGER, INTEGER };
enum sign : uint8_t { UNSET, POS, NEG };

struct Expression;
struct Definition;
struct Relational;
struct Dyadic;

struct Region {
  int start;
  int size;
  uint8_t sign;
  bool negative;

  Region *pos {nullptr};
  Region *neg {nullptr};
  
  Region (int start, int size, uint8_t sign = UNSET)
    : start {start}, size {size}, sign {sign}, negative {false} {
    if (sign == UNSET) {
      pos = new Region {start, size, POS};
      neg = new Region {start + size, size, NEG};
    }
  }

  ~Region () {
    delete pos;
    delete neg;
  }

  void set_sign (uint8_t new_sign) {
    if (new_sign == UNSET)
      { return; }

    if (sign == UNSET) {
      Region *choice {new_sign == POS ? pos : neg};
      start = choice->start;
      size = choice->size;
      sign = new_sign;

      delete pos;
      delete neg;
      neg = pos = nullptr;
    }
  }
};
    
std::ostream &operator << (std::ostream &out, Region &region) {
  out << region.start << ' ' << region.size << ' ' << (int) region.sign;
  return out;
}

class Formula {
  std::map<std::string, Region *> sets;
  std::set<std::string> abstract_sets;
  std::map<std::string, Definition *> comparison_handlers;
  std::map<std::string, Relational *> relational_handlers;
  std::map<std::string, Definition *> definition_handlers;
  std::map<std::string, Expression *> operand_handlers;
  std::set<std::string> predefined_literals;
  std::set<std::string> bound_variables;
  std::set<std::string> lambda_formulae;
#ifdef AUX_MESSAGE
  std::map<int, std::string> aux_vars;
#endif
  std::vector<int> abstract_variables;
  std::stringstream pb_body;
  std::string pb_name;
  int next_var {1}, nbclauses {0}, nbequals {0}, intsize {0};
  int upper_bound {};

  inline int complement (int);
  inline void construct_new_set (std::string &, int, uint8_t = UNSET, bool = false);
  inline void make_clause (std::vector<int> &&, int = 1, std::string = ">=");
  inline void make_clause (std::vector<int> &&, std::vector<std::string> &&, int, std::string = ">=");

  inline void update_intsize (int size) {
    size = (int) (log2 (size));
    if (++size > intsize)
      { intsize = size; }
  }
  
public:
  Formula (int, std::string);
  ~Formula ();
  inline bool explore_context (xml_node);
#ifdef AUX_MESSAGE
  int make_aux_var (std::string message) {
    int aux {next_var++};
    aux_vars[aux] = message;
    return aux;
  }

  void list_aux () {
    std::clog << "Auxiliaries:\n";
    for (auto &[left, right] : aux_vars) {
      std::clog << left << ":\n";
      std::clog << right << "\n\n";
    }
  }

  void list_sets () {
    std::clog << "Sets:\n";
    std::ranges::for_each
      (sets, [] (auto &x) {
	std::clog << x.first << ": "
		  << *(x.second) << '\n';
      });
  }

  void highlight_abstract_sets () {
    std::clog << "Abstract:\n";
    std::ranges::for_each
      (abstract_sets, [] (auto &x) { std::clog << x << '\n'; });
  }
#endif

  friend struct Dyadic;

  friend struct SetDifference;
  friend struct Intersection;
  friend struct Union;
  
  friend struct Comparison;
  friend struct ElementOf;
  friend struct SubsetOf;
  friend struct ProperSubsetOf;
  friend struct Equality;
  friend struct NotCompared;
  friend struct GreaterEqual;
  friend struct GreaterThan;
  friend struct LessThan;
  friend struct LessEqual;

  friend struct Surjection;
  friend struct SetOfRelations;
  friend struct TotalInjection;
  friend struct Bijection;

  friend struct Set;
  friend struct BinaryPred;
  friend struct ExpComparison;
  friend struct QuantifiedPred;
  friend struct UnaryPred;
  friend struct NaryPred;

  friend struct UnaryExp;
  friend struct BinaryExp;
  friend struct NaryExp;
  friend struct BooleanLiteral;
  friend struct EmptySet;
  friend struct Id;
  friend struct IntegerLiteral;

  friend class SetSizer;

  void print_opt (std::ostream &out) {
    out << "min:";
    for (int var : abstract_variables)
      { out << " +1 x" << var; }
    out << ";\n";
  }
  
  void print_pb (std::string &&out_name = "") {
    std::ofstream out {out_name};
    
    out << "* #variable= " << next_var - 1
	<< " #constraint= " << nbclauses
	<< " #equal= " << nbequals
	<< " intsize= " << intsize << '\n';
    if (!abstract_variables.empty ())
      { print_opt (out); }
    out << pb_body.str ();
  }

  void get_abstract_variables () {
    auto step_through_abs
      { [this] (const std::string &name) {
	Region *abs_set {sets[name]};
	for (int i {0}; i < abs_set->size; ++i)
	  { abstract_variables.push_back (abs_set->start + i); }
      }};
    
    for (const std::string &name : abstract_sets)
      { step_through_abs (name); }
  }

  void abstract_variables_to_file (const char *orig_pog, std::string &filename) {
    std::ofstream out {filename};
    out << orig_pog << '\n';
    for (auto &abs : abstract_sets)
      { out << abs << ' ' << *sets[abs] << '\n'; }
  }
};

std::string get_pb_file_name (char *pog_name, bool optimization) {
  std::string read_in_file {pog_name};
  read_in_file = read_in_file.substr (read_in_file.rfind ('/', read_in_file.rfind ('/') - 1) + 1);
  std::ranges::replace (read_in_file, '/', '-');
  std::string extension {optimization ? "pbo" : "pbs"};
  read_in_file.replace (read_in_file.rfind ("pog"), 3, extension);
  return read_in_file;
}

class SetSizer {
  std::stringstream tmp_buffer;
  Formula *formula;
  int degree;
  int selector;
  int pos_lim;
  int neg_lim;
			     
  void run_through (std::vector<std::string> &V, char sign, std::stringstream &out) {
    for (auto el_of_v {V.begin ()}; el_of_v != V.end (); ++el_of_v) {
      if ((*el_of_v)[0] == '-' || (*el_of_v)[0] >= '0' && (*el_of_v)[0] <= '9') {
	int change {std::stoi (*el_of_v)};
	if (sign == '-')
	  { change *= -1; }
	degree += change;
	V.erase (el_of_v);
	--el_of_v;
      }

      else {
	Region *region {formula->sets[*el_of_v]};
	int size {region->size};
	
	if (region->sign == UNSET) {
	  size >>= 1;
	  pos_lim += size;
	  neg_lim += size;

	  char neg_sign {sign == '+' ? '-' : '+'};
	  int pos_var {region->pos->start};
	  int neg_var {region->neg->start};
	  
	  for (int i {0}; i < region->size; ++i) {
	    out << sign << "1 x" << pos_var++ << ' '
		<< neg_sign << "1 x" << neg_var++ << ' ';
	  }
	}
	
	else {
	  char inner_sign {sign};
	  int var {region->start};
	  
	  if (region->sign == NEG)
	    { inner_sign = sign == '+' ? '-' : '+'; }

	  if (inner_sign == '+')
	    { pos_lim += region->size; }
	  else
	    { neg_lim += region->size; }
	  
	  for (int i {0}; i < region->size; ++i)
	    { out << inner_sign << "1 x" << var++ << ' '; }
	}
      }
    }
  }
	
  inline void if_var (std::vector<std::string> &positives,
		      std::vector<std::string> &negatives) {
    // M := α - |pos|

    std::stringstream tmp_buffer;

    neg_lim = pos_lim = 0;
    
    run_through (negatives, '+', tmp_buffer);
    run_through (positives, '-', tmp_buffer);

    int M {degree - pos_lim};
    if (M >= 0)
      { formula->pb_body << '+' << M; }
    else
      { formula->pb_body << M; }
    formula->pb_body << " x" << selector << ' ';

    formula->pb_body << tmp_buffer.str ();

    formula->pb_body << ">= " << -pos_lim << ";\n";

    ++formula->nbclauses;

    int size {abs (M) + neg_lim + (pos_lim << 1)};
    size = (int) (log2 (size));
    if (++size > formula->intsize)
      { formula->intsize = size; }
  }

  inline void if_pbexpr (std::vector<std::string> &positives,
			 std::vector<std::string> &negatives) {
    // M := |neg| + α + 1

    neg_lim = pos_lim = 0;
    
    run_through (positives, '+', formula->pb_body);
    run_through (negatives, '-', formula->pb_body);

    int M {neg_lim + degree + 1};
    if (M >= 0)
      { formula->pb_body << '+' << M; }
    else
      { formula->pb_body << M; }
    formula->pb_body << " x" << selector
		     << " >= " << degree + 1 << ";\n";

    ++formula->nbclauses;

    int size {pos_lim + (neg_lim + abs (degree + 1) << 1)};
    size = (int) (log2 (size));
    if (++size > formula->intsize)
      { formula->intsize = size; }
  }

public:
  SetSizer (Formula *formula)
    : formula {formula},
      pos_lim {0},
      neg_lim {0} {}
  
  inline int operator () (std::vector<std::string> &&positives,
			  std::vector<std::string> &&negatives,
			  int alpha) {
    // Always of the the form Σpos - Σneg <= α
    // Returns selector variable

#ifdef AUX_MESSAGE
    std::string message {"SetSizer\n"};
    for (std::string &name : positives)
      { message += "+ " + name + ' '; }
    message += '\n';
    for (std::string &name : negatives)
      { message += "- " + name + ' '; }
    message += '\n';
    message += "α = " + std::to_string (alpha);

    selector = formula->make_aux_var (message);
    
#else
    selector = formula->next_var++;

#endif
    
    degree = alpha;

    if_var (positives, negatives);
    if_pbexpr (positives, negatives);
    
    return selector;
  }
};

struct Expression {
  virtual std::string operator () (xml_node, Formula *) = 0;
};

struct Definition {
  virtual int operator () (xml_node, Formula *) = 0;
};

struct Dyadic {
protected:
  std::string operand1;
  std::string operand2;
  
  void get_operands (xml_node comparison, Formula *formula) {
    auto handle_operand {[formula] (xml_node operand) {
      if (!formula->operand_handlers.contains (operand.name ()))
	{ return std::string {}; }
      Expression *handler {formula->operand_handlers[operand.name ()]};
      return (*handler) (operand, formula);
    }};

    operand1 = handle_operand (comparison.first_child ());
    if (operand1.empty ())
      { return; }
    operand2 = handle_operand (comparison.first_child ().next_sibling ());
  }

public:
  std::string operand_as_str (int op) {
    switch (op) {
    case 1:
      return operand1;
      break;
    case 2:
      return operand2;
      break;
    default:
      return "";
    }
  }
};

struct Comparison : public Definition, public Dyadic {};

struct Relational : public Comparison {};

struct SetOperation : public Expression, public Dyadic {};

struct SetDifference : public SetOperation {
  inline std::string operator () (xml_node difference, Formula *formula) {
    get_operands (difference, formula);
    if (operand2.empty ())
      { return operand2; }

    std::string name {"(-s)(" + operand1 + ',' + operand2 + ')'};

    if (!formula->sets.contains (name)) {
      formula->construct_new_set (name, formula->sets[operand1]->size, POS);
      
      SetSizer set_sizer {formula};
      set_sizer ({name}, {operand1}, 0);
    }
    
    return name;
  }
};

struct Intersection : public SetOperation {
  inline std::string operator () (xml_node intersection, Formula *formula) {
    get_operands (intersection, formula);
    if (operand2.empty ())
      { return operand2; }
    if (operand2 < operand1)
      { std::swap (operand1, operand2); }

    std::string name {"(/\\)(" + operand1 + ',' + operand2 + ')'};

    if (!formula->sets.contains (name)) {
      formula->construct_new_set (name,
				  (formula->sets[operand1]->size < formula->sets[operand2]->size
				   ? formula->sets[operand1]->size : formula->sets[operand2]->size), POS);

      SetSizer set_sizer {formula};
      for (auto &op : {operand1, operand2})
	{ set_sizer ({name}, {op}, 0); }
    }

    return name;
  }
};

struct Union : public SetOperation {
  inline std::string operator () (xml_node set_union, Formula *formula) {
    get_operands (set_union, formula);
    if (operand2.empty ())
      { return operand2; }
    if (operand2 < operand1)
      { std::swap (operand1, operand2); }

    std::string name {"(\\/)(" + operand1 + ',' + operand2 + ')'};

    if (!formula->sets.contains (name)) {
      formula->construct_new_set (name,
				  (formula->sets[operand1]->size < formula->sets[operand2]->size
				   ? formula->sets[operand2]->size : formula->sets[operand1]->size), POS);

      SetSizer set_sizer {formula};
      for (auto &op : {operand1, operand2})
	{ set_sizer ({op}, {name}, 0); }
    }

    return name;
  }
};

struct Id : public Expression {
  inline std::string operator () (xml_node operand, Formula *formula) {
    std::string value {operand.attribute ("value").value ()};
    if (!formula->bound_variables.contains (value)
	&& !formula->sets.contains (value)) {
      if (formula->predefined_literals.contains (value)) {
	if (!formula->sets.contains (value)) {
	  switch (value[0]) {
	  case 'B':
	    formula->construct_new_set (value, 2, POS);
	    break;
	  default:
	    formula->construct_new_set (value, 0, POS);
	  }
	}
      }
      else 
	{ formula->construct_new_set (value, formula->upper_bound); }
    }
    
    return value;
  }
};

struct IntegerLiteral : public Expression {
  inline std::string operator () (xml_node operand, Formula *formula) {
    return operand.attribute ("value").value ();
  }
};

struct UnaryExp : public Expression {
  inline std::string operator () (xml_node expression, Formula *formula) {
    xml_node child {expression.first_child ()};
    if (formula->operand_handlers.contains (child.name ())) {
      Expression *handler {formula->operand_handlers[child.name ()]};
      std::string child_name {(*handler) (child, formula)};
      if (child_name.empty ())
	{ return child_name; }

      std::map<std::string, int> unary_operators
	{{"imax", 0}, {"imin", 1}, {"card", 2}, {"FIN", 3}, {"-i", 4}, {"perm", 5}};
      std::string op {expression.attribute ("op").value ()};

      if (!unary_operators.contains (op))
	{ return ""; }

      switch (unary_operators[op]) {
      case 0:
      case 1:
	op.insert (0, 1, '(');
	op.append (")");
	child_name = op + child_name;
	if (!formula->sets.contains (child_name))
	  { formula->construct_new_set (child_name, formula->upper_bound); }
	return child_name;
	
      case 2:
	return child_name;

      case 3:
	return "FIN(" + child_name + ')';

      case 4:
	if (child_name[0] == '-')
	  { return child_name.substr (1); }
	else if (child_name[0] >= '0' && child_name[0] <= '9')
	  { return "-" + child_name; }
	else {
	  int size {formula->sets[child_name]->size};
	  uint8_t sign {formula->sets[child_name]->sign};
	  const auto prefix {std::string {"(-)"}.length ()};
	  if (child_name.substr (0, prefix) == "(-)") {
	    child_name = child_name.substr (3);
	    if (!formula->sets.contains (child_name))
	      { formula->construct_new_set (child_name, size, (sign << 1) % 3); }
	  }
	  else {
	    child_name = "(-)" + child_name;
	    if (!formula->sets.contains (child_name))
	      { formula->construct_new_set (child_name, size, (sign << 1) % 3); }
	  }
	  return child_name;
	}

      case 5:
	return "(perm)" + child_name;
      }
	    
    }
    return "";
  }
};
   
struct BinaryExp : public Expression {
  inline std::string operator () (xml_node expression, Formula *formula) {
    std::string op {expression.attribute ("op").value ()};
    if (formula->relational_handlers.contains (op)) {
      Relational *handler {formula->relational_handlers[op]};
      if ((*handler) (expression, formula) < 0)
	{ return ""; }

      std::string name {"(" + op + ")("};
      name += handler->operand_as_str (1);
      name += ",";
      name += handler->operand_as_str (2);
      name += ")";
      return name;
    }

    if (op == "-s") {
      SetDifference handler;
      return handler (expression, formula);
    }
    else if (op == "/\\") {
      Intersection handler;
      return handler (expression, formula);
    }
    else if (op == "\\/") {
      Union handler;
      return handler (expression, formula);
    }

    auto handle_operand
      { [formula] (xml_node operand) {
	Expression *handler {formula->operand_handlers[operand.name ()]};
	return (*handler) (operand, formula);
      }};

    auto check_for_literal { [] (std::string &operand) {
      return (operand[0] == '-' || operand[0] >= '0' && operand[0] <= '9'); }
    };
      
    auto measure_operand
      { [formula, &check_for_literal] (std::string &operand) {
	if (check_for_literal (operand))
	  { return std::stoi (operand); }
	return formula->sets[operand]->size;
      }};
    
    if (op == ".." || op.find ('i') == 1) {
      xml_node first_child {expression.first_child ()};

      std::string operand1 {handle_operand (first_child)};
      if (operand1.empty ())
	{ return ""; }

      xml_node second_child {first_child.next_sibling ()};
      std::string operand2 {handle_operand (second_child)};
      if (operand2.empty ())
	{ return ""; }

      switch (op[0]) {
      case '.':
	{
	  if (operand1 == "0")
	    { return operand2; }
	  if (operand1 > operand2)
	    { std::swap (operand1, operand2); }
	  std::string name {"(..)(" + operand1 + "," + operand2 + ")"};

	  if (formula->sets.contains (name))
	    { return name; }

	  int size {check_for_literal (operand1) && check_for_literal (operand2)
		    ? stoi (operand2) - stoi (operand1) + 1
		    : (measure_operand (operand1) > measure_operand (operand2)
		       ? measure_operand (operand1) : measure_operand (operand2))};
	  // Will run into issues if op1 and op2 have opposite signs.

	  formula->construct_new_set (name, size, POS);

	  SetSizer set_sizer {formula};
	  set_sizer ({name, operand1}, {operand2}, 0);
	  set_sizer ({operand2}, {name, operand1}, 0);

	  return name;
	}
	
      case '+':
	{
	  if (check_for_literal (operand1) && check_for_literal (operand2)) {
	    int literal_size {std::stoi (operand1) + std::stoi (operand2)};
	    return std::to_string (literal_size);
	  }
	  
	  if (operand1 > operand2)
	    { std::swap (operand1, operand2); }
	  std::string name {"(+)(" + operand1 + ',' + operand2 + ')'};
	  int size {abs (measure_operand (operand1)) + abs (measure_operand (operand2))};
	  formula->construct_new_set (name, size);

	  SetSizer set_sizer {formula};
	  set_sizer ({name}, {operand1, operand2}, 0);
	  set_sizer ({operand1, operand2}, {name}, 0);

	  return name;
	}
	
      case '-':
	{
	  if (check_for_literal (operand1) && check_for_literal (operand2)) {
	    int literal_size {std::stoi (operand1) - std::stoi (operand2)};
	    return std::to_string (literal_size);
	  }
	  
	  std::string name {"(" +operand1 + '-' + operand2 + ')'};
	  if (formula->sets.contains (name))
	    { return name; }
	  
	  int measure1 {measure_operand (operand1)};
	  int measure2 {measure_operand (operand2)};
	  int size {abs (measure1) + abs (measure2)};
	
	  formula->construct_new_set (name, size);

	  SetSizer set_sizer {formula};
	  set_sizer ({name, operand2}, {operand1}, 0);
	  set_sizer ({operand1}, {name, operand2}, 0);

	  return name;
	}

      case '*':
	{
	  if (check_for_literal (operand1) && check_for_literal (operand2)) {
	    int literal_size {std::stoi (operand1) * std::stoi (operand2)};
	    return std::to_string (literal_size);
	  }

	  if (operand1 > operand2)
	    { std::swap (operand1, operand2); }

	  std::string name {"(*)(" + operand1 + ',' + operand2 + ')'};
	  if (formula->sets.contains (name))
	    { return name; }

	  int product_size {abs (measure_operand (operand1)) * abs (measure_operand (operand2))};
	  formula->construct_new_set (name, product_size);	    

	  auto multiplication
	    { [formula, name] (std::string &operand1,
			       std::string &operand2) {
	      formula->make_clause ({1, -std::stoi (operand1)}, {name, operand2}, 0);
	      formula->make_clause ({std::stoi (operand1), -1}, {operand2, name}, 0);
	    }};
	  
	  if (check_for_literal (operand1)) {
	    multiplication (operand1, operand2);
	    return name;
	  }
	  else if (check_for_literal (operand2)) {
	    multiplication (operand2, operand1);
	    return name;
	  }
	}
	  
	std::cerr << "*i between variables!\n";
	
	return "";
	
      case '/':
	{
	  if (check_for_literal (operand1) && check_for_literal (operand2)) {
	    int literal_size {std::stoi (operand1) / std::stoi (operand2)};
	    return std::to_string (literal_size);
	  }

	  std::string name {"(/)(" + operand1 + ',' + operand2 + ')'};
	  if (formula->sets.contains (name))
	    { return name; }

	  formula->construct_new_set (name, measure_operand (operand1));

	  if (check_for_literal (operand2)) {
	    formula->make_clause ({std::stoi (operand2), -1}, {name, operand1}, 0);
	    formula->make_clause ({1, -std::stoi (operand2)}, {operand1, name}, 0);
	    return name;
	  }

	  std::cerr << "/i only handled between integer literals or if denominator is an integer literal\n";
	}
	
      default:
	return "";
      }
    } 
    return "";
  }
};

struct NaryExp : public Expression {
  inline std::string operator () (xml_node expression, Formula *formula) {
    if (std::string {"{"} == expression.attribute ("op").value ()) {
      std::set<std::string> elements;
      int cardinality {0};
      for (xml_node child : expression.children ()) {
	++cardinality;
	
	Expression *handler {formula->operand_handlers[child.name ()]};
	std::string element {(*handler) (child, formula)};
	// Consider size. If elements are unhandled, not important for now.
	// if (element == "")
	//   { return element; }
	elements.insert (element);
      }

      int var {formula->next_var};
      std::string set_name {"(" + std::to_string (cardinality) + "){"};
      
      auto el_iter {elements.begin ()};
      set_name += *el_iter;
    
      for (++el_iter; el_iter != elements.end (); ++el_iter)
	{ set_name += "," + *el_iter; }
      set_name += "}";
    
      if (!formula->sets.contains (set_name)) {
	formula->construct_new_set (set_name, cardinality, POS);
	std::vector<int> vars (cardinality);
	std::iota (vars.begin (), vars.end (), var);
	formula->make_clause (std::move (vars), cardinality);
	formula->next_var += cardinality;
      }

      return set_name;
    }

    return "";
  }
};
    
struct EmptySet : public Expression {
  inline std::string operator () (xml_node, Formula *formula) {
    if (!formula->sets.contains ("{}")) {
      int var {formula->next_var++};
      formula->sets["{}"] = new Region {var, 1};
      formula->make_clause ({-var});
    }
    return "{}";
  }
};

struct BooleanLiteral : public Expression {
  inline std::string operator () (xml_node literal, Formula *formula) {
    std::string polarity {literal.attribute ("value").value ()};
    if (polarity == "TRUE") {
      if (!formula->sets.contains (polarity)) {
	int var {formula->next_var++};
	formula->sets["TRUE"] = new Region {var, 1};
	formula->make_clause ({var});
      }
      return "TRUE";
    }
    else {
      EmptySet falsehood;
      return falsehood (literal, formula);
    }
  }
};

struct ElementOf : public Comparison {
private:
  std::set<std::string> relational
  {"+->", "+->>", "-->", "-->>", "<->", ">+>", ">->", ">->>"};
  // {"<+", "<<|", "<|", "><"}

public:
  inline int operator () (xml_node comparison, Formula *formula) {
    xml_node second_child {comparison.first_child ().next_sibling ()};
    if (std::string {"Binary_Exp"} == second_child.name ()
	&& relational.contains (second_child.attribute ("op").value ())) {
      std::string op {second_child.attribute ("op").value ()};
      if (!formula->relational_handlers.contains (op))
	{ return -1; }

      Relational *handler {formula->relational_handlers[op]};

      int func {(*handler) (second_child, formula)};
      
      std::string definiendum {comparison.first_child ().attribute ("value").value ()};
      if (func < 0 || formula->bound_variables.contains (definiendum))
	{ return func; }

      std::string rhs_dom {handler->operand_as_str (1)};
      std::string rhs_ran {handler->operand_as_str (2)};
      std::string dom {"dom(" + definiendum + ")"};
      std::string ran {"ran(" + definiendum + ")"};
      if (!formula->sets.contains (dom))
	{ formula->construct_new_set (dom, formula->sets[rhs_dom]->size, POS); }
      if (!formula->sets.contains (ran))
	{ formula->construct_new_set (ran, formula->sets[rhs_ran]->size, POS); }

      std::vector<int> conjuncts {func};
      conjuncts.reserve (7);

      SetSizer set_sizer {formula};

      conjuncts.push_back (set_sizer ({dom}, {rhs_dom}, 0));
      if (op.find ('+') == op.npos)
	{ conjuncts.push_back (set_sizer ({rhs_dom}, {dom}, 0)); }

      EmptySet empty_set;
      conjuncts.push_back (set_sizer ({empty_set (comparison, formula)}, {ran}, -1));

      conjuncts.push_back (set_sizer ({ran}, {rhs_ran}, 0));
      if (op.rfind (">>") == op.npos)
	{ conjuncts.push_back (set_sizer ({rhs_ran}, {ran}, 0)); }

#ifdef AUX_MESSAGE
      std::string message {definiendum + " : " + rhs_dom + op + rhs_ran};
      int binding_var {formula->make_aux_var (message)};

#else
      int binding_var {formula->next_var++};

#endif

      for (int conjunct : conjuncts)
	{ formula->make_clause ({-binding_var, conjunct}); }

      std::ranges::transform (conjuncts, conjuncts.begin (), [] (int c) { return c * -1; });
      conjuncts.push_back (binding_var);
      formula->make_clause (std::move (conjuncts));

      return binding_var;
    }

    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }

#ifdef AUX_MESSAGE
    std::string message {operand1 + " : " + operand2};
    int binding_var {formula->make_aux_var (message)};

#else
    int binding_var {formula->next_var++};

#endif
    
    auto non_empty_func
      { [formula] (int start, int size, int flag) {
	std::vector<int> variables (size);
	std::iota (variables.begin (), variables.end (), start);
	std::ranges::for_each (variables,
			       [formula, flag] (int var)
			       { formula->make_clause ({-var, flag}); });
	variables.push_back (-flag);
	formula->make_clause (std::move (variables));
      }};
    
    if (operand2 == "NAT1") {
      formula->sets[operand1]->set_sign (POS);
      
      std::vector<int> variables (formula->sets[operand1]->size);
      std::iota (variables.begin (), variables.end (), formula->sets[operand1]->start);
      formula->make_clause (std::move (variables));
      return binding_var;
    }

    if (!formula->predefined_literals.contains (operand2)) {
      const auto perm {std::string {"(perm)"}.length ()};
      const auto fin {std::string {"FIN("}.length ()};
      
      if (operand2.substr (0, perm) == "(perm)") {
	operand2 = operand2.substr (perm);
	
	SetSizer set_sizer {formula};
	int forwards {set_sizer ({operand1}, {operand2}, 0)};
	int backwards {set_sizer ({operand2}, {operand1}, 0)};

	for (int dir : {forwards, backwards})
	  { formula->make_clause ({-binding_var, dir}); }
	formula->make_clause ({-forwards, -backwards, binding_var});
      }
	
      else if (operand2.substr (0, fin) == "FIN(")
	{}
      else
	{ non_empty_func (formula->sets[operand2]->start, formula->sets[operand2]->size, binding_var); }
    }

    return binding_var;
  }
};
	
struct Equality : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    if (comparison.child ("Quantified_Exp")) {
      xml_node first_child {comparison.first_child ()};
      if (std::string {"Id"} == first_child.name ()) {
	formula->lambda_formulae.insert (first_child.attribute ("value").value ());
	if (!formula->sets.contains ("TRUE")) {
	  int var {formula->next_var++};
	  formula->sets["TRUE"] = new Region {var, 1};
	  formula->make_clause ({var});
	}
	return formula->sets["TRUE"]->start;
      }
      else
	{ return -1; }
    }
	
    // Currently only works for comparing integers although the operator is overloaded in Atelier B.
    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }
    auto check_for_literal { [] (std::string &name) {
      return name[0] == '-' || name[0] >= '0' && name[0] <= '9';
    }};
    auto invert_negative { [formula, &check_for_literal] (std::string &operand1, std::string &operand2) {
      if (check_for_literal (operand2)) {
	formula->sets[operand1]->negative = true;
      }
    }};

    invert_negative (operand1, operand2);
    invert_negative (operand2, operand1);

    SetSizer set_sizer {formula};
    int forwards {set_sizer ({operand1}, {operand2}, 0)};
    int backwards {set_sizer ({operand2}, {operand1}, 0)};

#ifdef AUX_MESSAGE
    std::string message {operand1 + " = " + operand2};
    int equality {formula->make_aux_var (message)};

#else
    int equality {formula->next_var++};

#endif
    
    for (int dir : {forwards, backwards})
      { formula->make_clause ({-equality, dir}); }
    formula->make_clause ({-forwards, -backwards, equality});

    return equality;
  }
};

struct GreaterEqual : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }
    
    SetSizer set_sizer {formula};
    return set_sizer ({operand2}, {operand1}, 0);
  }
};

struct GreaterThan : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }

    SetSizer set_sizer {formula};
    return set_sizer ({operand2}, {operand1}, -1); 
  }
};

struct LessThan : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }

    SetSizer set_sizer {formula};
    return set_sizer ({operand1}, {operand2}, -1); 
  }
};

struct LessEqual : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }

    SetSizer set_sizer {formula};
    return set_sizer ({operand1}, {operand2}, 0); 
  }
};

struct NotCompared : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }
    return formula->next_var++;
  }
};

struct Surjection : public Relational {
  inline int operator () (xml_node relation, Formula *formula) {
    GreaterEqual ge;
    int selector {ge (relation, formula)};
    if (selector >= 0) {
      operand1 = ge.operand_as_str (1);
      operand2 = ge.operand_as_str (2);
    }
    
    return selector;
  }
};

struct SetOfRelations : public Relational {
  inline int operator () (xml_node relation, Formula *formula) {
    NotCompared nc;
    int selector {nc (relation, formula)};
    if (selector >= 0) {
      operand1 = nc.operand_as_str (1);
      operand2 = nc.operand_as_str (2);
    }
    
    return selector;
  }
};

struct TotalInjection : public Relational {
  inline int operator () (xml_node relation, Formula *formula) {
    LessEqual le;
    int selector {le (relation, formula)};
    if (selector >= 0) {
      operand1 = le.operand_as_str (1);
      operand2 = le.operand_as_str (2);
    }
    
    return selector;
  }
};

struct Bijection : public Relational {
  inline int operator () (xml_node relation, Formula *formula) {
    Equality eq;
    int selector {eq (relation, formula)};
    if (selector >= 0) {
      operand1 = eq.operand_as_str (1);
      operand2 = eq.operand_as_str (2);
    }
    
    return selector;
  }
};

struct Set : public Definition {
  inline int operator () (xml_node set, Formula *formula) {
    std::string id {set.child ("Id").attribute ("value").value ()};

    int var {formula->next_var};

    auto fresh_construct {
      [formula, &id, var] (int size, bool abstract) {
	formula->construct_new_set (id, size, POS, abstract);
	std::vector<int> vec (size);
	std::iota (vec.begin (), vec.end (), var);
	return vec;
      }};
    
    if (set.child ("Enumerated_Values")) {
      int size = 0;
      for (auto el : set.child ("Enumerated_Values").children ())
	{ ++size; } 
      formula->make_clause (fresh_construct (size, false), size);
    }
    else
      { formula->make_clause (fresh_construct (formula->upper_bound, true)); }

    return var;
  }
};
  
struct PredGroup : public Definition {};

struct BinaryPred : public PredGroup {
  inline int operator () (xml_node predicate, Formula *formula) {
    if (std::ranges::any_of (predicate.children (),
			     [formula] (xml_node child) 
			     { return !formula->definition_handlers.contains (child.name ()); }))
      { return -1; }

    auto get_seq_part {[formula] (xml_node child) -> int {
      Definition *handler {formula->definition_handlers[child.name ()]};
      return (*handler) (child, formula);
    }};

    std::array<int, 3> variables;
    std::ranges::transform (predicate.children (), variables.begin (),
			    [formula] (xml_node child) {
			      Definition *handler {formula->definition_handlers[child.name ()]};
			      return (*handler) (child, formula);
			    });
    if (std::any_of (variables.begin (), std::next (variables.begin (), 2),
		     [] (int x) { return x < 0; }))
      { return -1; }

#ifdef AUX_MESSAGE
    std::string message {std::to_string (variables[0]) + predicate.attribute ("op").value () + std::to_string (variables[1])};
    int binary_pred {formula->make_aux_var (message)};

#else
    int binary_pred {formula->next_var++};

#endif
    
    variables[2] = binary_pred;

    if (predicate.attribute ("op").value ()[0] != '<') {
      formula->make_clause ({-variables[1], binary_pred});
      formula->make_clause ({variables[0], binary_pred});
      formula->make_clause ({-binary_pred, -variables[0], variables[1]});
    }
    else {
      for (int i {0}; i < 3; ++i)
	{ formula->make_clause ({-variables[i % 3], -variables[(i + 1) % 3], variables[(i + 2) % 3]}); }
      formula->make_clause ({variables[0], variables[1], variables[2]});
    }
    return binary_pred;
  }
};

struct ExpComparison : public PredGroup {
protected:
  inline int convexity_constraint (xml_node comparison) {
    if (std::string {"="} != comparison.attribute ("op").value ()
	|| std::string {"Id"} != comparison.first_child ().name ())
      { return 0; }
  
    xml_node second_child {comparison.first_child ().next_sibling ()};

    if (std::string {".."} == second_child.attribute ("op").value ()
	&& std::string {"imin"} == second_child.first_child ().attribute ("op").value ()
	&& std::string {"imax"} == second_child.first_child ().next_sibling ().attribute ("op").value ()) {
      std::string value {comparison.first_child ().attribute ("value").value ()};
      
      if (std::ranges::all_of (second_child.children (),
			       [&value] (auto &child) { return value == child.first_child ().attribute ("value").value (); }))
	{ return 2; }
      
      return 1;
    }
    return 0;
  }  

public:
  inline int operator () (xml_node comparison, Formula *formula) {
    std::string op {comparison.attribute ("op").value ()};
    if (!formula->comparison_handlers.contains (op))
      { return -1; }

    switch (convexity_constraint (comparison)) {
    case 2: 
      if (!formula->sets.contains ("TRUE")) {
	int var {formula->next_var++};
	formula->sets["TRUE"] = new Region {var, 1};
	formula->make_clause ({var});
      }
      return formula->sets["TRUE"]->start;
      
    case 1:
      xml_node first_child {comparison.first_child ()};
      if (!formula->operand_handlers.contains (first_child.name ()))
	{ return -1; }

      Expression *handler {formula->operand_handlers[first_child.name ()]};
      std::string first_child_name {(*handler) (first_child, formula)};
      if (first_child_name.empty ())
	{ return -1; }

      xml_node second_child {first_child.next_sibling ().first_child ().first_child ()};
      handler = formula->operand_handlers[second_child.name ()];
      std::string second_child_name {(*handler) (second_child, formula)};
      if (second_child_name.empty ())
	{ return -1; }

      SetSizer set_sizer {formula};
      return set_sizer ({second_child_name}, {first_child_name}, 0);
    }

    Definition *handler {formula->comparison_handlers[op]};
    return (*handler) (comparison, formula);
  }
};

struct QuantifiedPred : public PredGroup {
  inline int operator () (xml_node quantification, Formula *formula) {
    if (std::string {"!"} == quantification.attribute ("type").value ())
      { return -1; } // Universal quantification

    std::ranges::for_each (quantification.first_child ().children (),
			   [formula] (xml_node var)
			   { formula->bound_variables.insert (var.attribute ("value").value ()); });
    xml_node body {quantification.child ("Body").first_child ()};

    Definition *handler {formula->definition_handlers[body.name ()]};
    int pred_val {(*handler) (body, formula)};
    
    formula->bound_variables.clear ();
    
    return pred_val;
  }
};
    
struct UnaryPred : public PredGroup {
  inline int operator () (xml_node predicate, Formula *formula) {
    xml_node child {predicate.first_child ()};
    if (!formula->definition_handlers.contains (child.name ()))
      { return -1; }
    
    Definition *handler {formula->definition_handlers[child.name ()]};
    int negandum {(*handler) (child, formula)};

    if (negandum < 0)
      { return -1; }

    return formula->complement (negandum);
  }
};

struct NaryPred : public PredGroup {
  inline int operator () (xml_node predicate, Formula *formula) {
    if (std::ranges::any_of (predicate.children (),
			     [formula] (xml_node child) 
			     { return !formula->definition_handlers.contains (child.name ()); }))
      { return -1; }

    std::vector<int> juncts;

    for (xml_node child : predicate.children ()) {
      Definition *handler {formula->definition_handlers[child.name ()]};
      int junct {(*handler) (child, formula)};

      if (junct < 0)
	{ return -1; }
      juncts.push_back (junct);
    }

#ifdef AUX_MESSAGE
    std::string message {"("};
    message += predicate.attribute ("op").value ();
    for (int el : juncts)
      { message += " " + std::to_string (el); }
    message += ")";
    int junction_var {formula->make_aux_var (message)};

#else
    int junction_var {formula->next_var++};

#endif
    
    if (std::string {"&"} == predicate.attribute ("op").value ()) {
      std::ranges::for_each (juncts,
			     [formula, junction_var] (int v) {
			       formula->make_clause ({-junction_var, v});
			       v = -v;
			     });
      juncts.push_back (junction_var);
      formula->make_clause (std::move (juncts));
    }
    else { // if .op == "or"
      std::ranges::for_each (juncts,
			     [formula, junction_var] (int v)
			     { formula->make_clause ({-v, junction_var}); });
      juncts.push_back (-junction_var);
      formula->make_clause (std::move (juncts));
    }

    return junction_var;
  }
};
  
Formula::Formula (int k, std::string pb_name) 
  : upper_bound {k}, pb_name {pb_name},
    predefined_literals {"MAXINT", "MININT",
			 "NAT", "NAT1", "INT",
			 "BOOL"} {
  comparison_handlers[":"] = new ElementOf {};
  comparison_handlers["/:"] = new NotCompared {};
  comparison_handlers["<:"] = new LessEqual {};
  comparison_handlers["/<:"] = new NotCompared {};
  comparison_handlers["<<:"] = new LessThan {};
  comparison_handlers["/<<:"] = new NotCompared {};
  comparison_handlers["="] = new Equality {};
  comparison_handlers["/="] = new NotCompared {};
  comparison_handlers[">=i"] = new GreaterEqual {};
  comparison_handlers[">i"] = new GreaterThan {};
  comparison_handlers["<i"] = new LessThan {};
  comparison_handlers["<=i"] = new LessEqual {};

  relational_handlers["+->"] = new SetOfRelations {};
  relational_handlers["+->>"] = new Surjection {};
  relational_handlers["-->"] = new SetOfRelations {};
  relational_handlers["-->>"] = new Surjection {};
  relational_handlers["<->"] = new SetOfRelations {};
  relational_handlers[">+>"] = new SetOfRelations {};
  relational_handlers[">->"] = new TotalInjection {};
  relational_handlers[">->>"] = new Bijection {};
  
  definition_handlers["Set"] = new Set {};
  definition_handlers["Binary_Pred"] = new BinaryPred {};
  definition_handlers["Exp_Comparison"] = new ExpComparison {};
  definition_handlers["Quantified_Pred"] = new QuantifiedPred {};
  definition_handlers["Unary_Pred"] = new UnaryPred {};
  definition_handlers["Nary_Pred"] = new NaryPred {};

  operand_handlers["Unary_Exp"] = new UnaryExp {};
  operand_handlers["Binary_Exp"] = new BinaryExp {};
  operand_handlers["Nary_Exp"] = new NaryExp {};
  operand_handlers["Boolean_Literal"] = new BooleanLiteral {};
  operand_handlers["EmptySet"] = new EmptySet {};
  operand_handlers["Id"] = new Id {};
  operand_handlers["Integer_Literal"] = new IntegerLiteral {};
}

Formula::~Formula () {
  for (auto &map : {comparison_handlers, definition_handlers}) {
    for (auto &couple : map)
      { delete couple.second; }
  }
  for (auto &couple : relational_handlers)
    { delete couple.second; }
  for (auto &couple : operand_handlers)
    { delete couple.second; }
  for (auto &couple : sets)
    { delete couple.second; }
}
 
inline void Formula::construct_new_set (std::string &name, int size, uint8_t sign, bool abstract) {
  int var {next_var};
  if (sign == UNSET) {
    Region *new_region {new Region {var, size}};
    sets[name] = new_region;
    if (abstract)
      { abstract_sets.insert (name); }
    next_var = var + (size << 1);

#ifdef AUX_MESSAGE
    std::string message {"name non-negative"};
    int non_neg {make_aux_var (message)};

    message = "name non-positive";
    int non_pos {make_aux_var (message)};

#else
    int non_neg {next_var++};
    int non_pos {next_var++};

#endif

    auto if_empty {
      [this] (int selector, Region *region) {
	std::vector<int> vec (region->size);
	std::iota (vec.begin (), vec.end (), region->start);
	for (int i : vec)
	  { make_clause ({-selector, -i}, -1); }
      }};

    if_empty (non_neg, new_region->neg);
    if_empty (non_pos, new_region->pos);

    make_clause ({non_pos, non_neg}, 1);
  }
  else {
    sets[name] = new Region {var, size, sign};
    if (abstract)
      { abstract_sets.insert (name); }
    next_var = var + size;
  }
}

int Formula::complement (int negandum) {
#ifdef AUX_MESSAGE
  std::string message {"¬" + std::to_string (negandum)};
  int aux {make_aux_var (message)};

#else
  int aux {next_var++};

#endif

  make_clause ({-aux, negandum}, 1, "=");

  return aux;
}

bool Formula::explore_context (xml_node proof_obligations) {
  for (xml_node definition : proof_obligations.children ()) {
    std::string name {definition.attribute ("name").value ()};
    if (std::string {"Define"} == definition.name ()
	&& (name == "ctx"                                        
	    || name.substr (name.length () - 3) == "prp")) {
      for (xml_node interior : definition.children ()) {
	if (definition_handlers.contains (interior.name ())) {
	  Definition *handler {definition_handlers[interior.name ()]};
	  int flag {(*handler) (interior, this)};
	  if (flag > 0) {
	    if (std::string {"Set"} != interior.name ())
	      { make_clause ({flag}); }
	  }
	  else {
	    interior.print (std::cerr);
	    return false;
	  }
	}
	else {
	  std::cerr << interior.name () << '\n';
	  return false;
	}
      }
    }
  }
  return true;
}

void Formula::make_clause (std::vector<int> &&literals, int degree, std::string comparison) {
  int size {0};
  
  if (comparison == "=")
    { ++nbequals; }
  for (auto lit : literals) {
    ++size;
    if (lit < 0) {
      pb_body << "-1 x";
      --degree;
      lit *= -1;
    }
    else
      { pb_body << "+1 x"; }
    pb_body << lit << ' ';
  }
  pb_body << comparison << ' ' << degree << ";\n";
  ++nbclauses;

  update_intsize (size + abs (degree));
}

void Formula::make_clause (std::vector<int> &&W, std::vector<std::string> &&X, int K, std::string comparison) {
  int size {0};

  if (comparison == "=")
    { ++nbequals; }
  for (int i {0}; i < W.size (); ++i) {
    int max {sets[X[i]]->size};
    int x {sets[X[i]]->start};
    int coeff {W[i]};
    
    for (int j {0}; j < max; ++j) {
      if (coeff >= 0) {
	pb_body << '+';
	size += coeff;
      }
      else
	{ size += -coeff; }

      pb_body << coeff << " x" << x + j << ' ';
    }
  }

  pb_body << comparison << ' ' << K << ";\n";
  ++nbclauses;

  update_intsize (size + abs (K));
}

namespace XML_TO_SOLVER {
  bool run (const char *input_pog, int k, bool optimization) {
    std::filesystem::path in_file {input_pog};
    std::filesystem::path out_file {in_file.stem ().string () 
				    + (optimization ? ".pbo" : ".pbs")};

    Formula *formula {new Formula {k, out_file.c_str ()}};

    pugi::xml_document doc;
    doc.load_file (input_pog);

    if (!formula->explore_context (doc.first_child ()))
      { return false; }
    if (optimization)
      { formula->get_abstract_variables (); }
    formula->print_pb (out_file.string ());

    std::string abs_out {out_file.stem ().string () + ".abs_out"};
    formula->abstract_variables_to_file (input_pog, abs_out);

#ifdef AUX_MESSAGE
    formula->list_aux ();
    formula->list_set ();
    formula->highlight_abstract_sets ();
#endif

    delete formula;
    return true;
  }
}

// int main (int argc, char **argv) {
//   std::string help {"Usage: ./xml_to_solver <k> <POG gile> <pbs | pbo>\n"};
//   if (argc < 4) {
//     std::cerr << help;
//     return 1;
//   }

//   RunClock *clock {new RunClock {}};

//   bool optimization;
//   if (std::string (argv[3]) == "pbs")
//     { optimization = false; }
//   else if (std::string (argv[3]) == "pbo")
//     { optimization = true; }
//   else {
//     std::cerr << help;
//     return 1;
//   }
	
//   if (!XML_TO_SOLVER::run (argv[2], atoi (argv[1]), optimization)) {
//     std::cerr << "To PB failed.\n";
//     return 1;
//   }

//   std::cout << "To PB: ";
//   delete clock;
  
//   return 0;
// }

