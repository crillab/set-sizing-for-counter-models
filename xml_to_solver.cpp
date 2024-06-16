#include "pugixml.hpp"

#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <vector>

using xml_node = const pugi::xml_node &;

enum typref { POW_INTEGER, INTEGER };

struct Expression;
struct Definition;
struct Relational;

class Formula {
  std::map<std::string, std::array<int, 2>> sets;    // <"name", {first_var, size}
  std::map<std::string, Definition *> comparison_handlers;
  std::map<std::string, Relational *> relational_handlers;
  std::map<std::string, Definition *> definition_handlers;
  std::map<std::string, Expression *> operand_handlers;
  std::set<std::string> predefined_literals;
  std::set<std::string> bound_variables;
  #ifdef AUX_MESSAGE
  std::map<int, std::string> aux_vars;
  #endif
  std::stringstream pbs_body;
  std::string pbs_name;
  int next_var {1}, nbclauses {0}, nbequals {0}, intsize {0};
  int upper_bound {};

  inline int complement (int);
  inline int constrain_equality (std::string &, std::string &);
  inline int constrain_gte (std::string &, std::string &);
  inline void construct_new_set (std::string &, int);
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
  inline void explore_context (xml_node);
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
		  << x.second[0] << ' '
		  << x.second[1] << '\n';
      });
  }
  #endif
  
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
  
  void print_pbs () {
    std::cout << "* #variable= " << next_var - 1
	      << " #constraint= " << nbclauses
	      << " #equal= " << nbequals
	      << " intsize= " << intsize << '\n';
    std::cout << pbs_body.str ();
  }
};

inline bool convexity_constraint (xml_node comparison) {
  if (std::string {"Exp_Comparison"} != comparison.name ()
      || std::string {"="} != comparison.attribute ("op").value ()
      || std::string {"Id"} != comparison.first_child ().name ())
    { return false; }
  
  std::string value {comparison.first_child ().attribute ("value").value ()};
  xml_node second_child {comparison.first_child ().next_sibling ()};
  
  return
    std::string {".."} == second_child.attribute ("op").value () &&
    std::string {"imin"} == second_child.first_child ().attribute ("op").value () &&
    std::string {"imax"} == second_child.first_child ().next_sibling ().attribute ("op").value () &&
    std::ranges::all_of (second_child.children (),
			 [&value] (auto &child) { return value == child.first_child ().attribute ("value").value (); });
}  
  
std::string get_pbs_file_name (char *pog_name) {
  std::string read_in_file {pog_name};
  read_in_file = read_in_file.substr (read_in_file.rfind ('/', read_in_file.rfind ('/') - 1) + 1);
  std::ranges::replace (read_in_file, '/', '-');
  read_in_file.replace (read_in_file.rfind ("pog"), 3, "pbs");
  return read_in_file;
}

class SetSizer {
  std::stringstream tmp_buffer;
  Formula *formula;
  int degree;
  int selector;

  int get_limits (std::vector<std::string> &V) {
    return std::accumulate (V.begin (), V.end (), 0,
			    [this] (int acc, std::string &name)
			    { return acc + formula->sets[name][1]; });
  }
			     
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
	int var {formula->sets[*el_of_v][0]};
	for (int i {0}; i < formula->sets[*el_of_v][1]; ++i)
	  { out << sign << "1 x" << var++ << ' '; }
      }
    }
  }
	
  inline void if_var (std::vector<std::string> &positives,
		      std::vector<std::string> &negatives) {
    // M := α - |pos|

    std::stringstream tmp_buffer;
    
    run_through (negatives, '+', tmp_buffer);
    run_through (positives, '-', tmp_buffer);

    int positive_limits {get_limits (positives)};
    int M {degree - positive_limits};
    if (M >= 0)
      { formula->pbs_body << '+' << M; }
    else
      { formula->pbs_body << M; }
    formula->pbs_body << " x" << selector << ' ';

    formula->pbs_body << tmp_buffer.str ();

    formula->pbs_body << ">= " << -positive_limits << ";\n";

    ++formula->nbclauses;

    int size {abs (M) + get_limits (negatives) + (positive_limits << 1)};
    size = (int) (log2 (size));
    if (++size > formula->intsize)
      { formula->intsize = size; }
  }

  inline void if_pbexpr (std::vector<std::string> &positives,
			 std::vector<std::string> &negatives) {
    // M := |neg| + α + 1

    run_through (positives, '+', formula->pbs_body);
    run_through (negatives, '-', formula->pbs_body);

    int negative_limits {get_limits (negatives)};
    int M {negative_limits + degree + 1};
    if (M >= 0)
      { formula->pbs_body << '+' << M; }
    else
      { formula->pbs_body << M; }
    formula->pbs_body << " x" << selector
		      << " >= " << degree + 1 << ";\n";

    ++formula->nbclauses;

    int size {get_limits (positives) + (negative_limits + abs (degree + 1) << 1)};
    size = (int) (log2 (size));
    if (++size > formula->intsize)
      { formula->intsize = size; }
  }

public:
  SetSizer (Formula *formula) : formula {formula} {}
  
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

struct Comparison : public Definition {
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
};

struct Relational : public Comparison {
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

struct Id : public Expression {
  inline std::string operator () (xml_node operand, Formula *formula) {
    std::string value {operand.attribute ("value").value ()};
    if (!formula->predefined_literals.contains (value)
	&& !formula->bound_variables.contains (value)
	&& !formula->sets.contains (value)) 
      { formula->construct_new_set (value, formula->upper_bound); }

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
      if (std::string {"FIN"} == expression.attribute ("op").value ()) {
	Expression *handler {formula->operand_handlers[child.name ()]};
	return "FIN(" + (*handler) (child, formula);
      }
      else if (std::string {"card"} == expression.attribute ("op").value ()) {
	Expression *handler {formula->operand_handlers[child.name ()]};
	return (*handler) (child, formula);
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
	return formula->sets[operand][1];
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
	  if (operand1 > operand2)
	    { std::swap (operand1, operand2); }
	  std::string name {"(..)(" + operand1 + "," + operand2 + ")"};

	  if (formula->sets.contains (name))
	    { return name; }
	  
	  int size {check_for_literal (operand1) && check_for_literal (operand2)
		    ? stoi (operand2) - stoi (operand1) + 1
	            : (formula->sets[operand1][1] > formula->sets[operand2][1]
		       ? formula->sets[operand1][1] : formula->sets[operand2][1])};
	               // Will run into issues if op1 and op2 have opposite signs.

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
	  int size {measure_operand (operand1) + measure_operand (operand2)};
	  if (size < 0) {
	    name = "(-)" + name;
	    size *= 1;
	  }
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
	  
	  std::string name {"(-)(" +operand1 + ',' + operand2 + ')'};
	  if (formula->sets.contains (name))
	    { return name; }
	  
	  int measure1 {measure_operand (operand1)};
	  int measure2 {measure_operand (operand2)};
	  int size;
	
	  constexpr int neg_flag {1 << sizeof (int) * 8 - 1};
	  if (measure1 & neg_flag ^ measure2 & neg_flag)
	    { size = abs (measure1) > abs (measure2) ? measure1 : measure2; }
	  else
	    { size = measure1 + measure2; }
	  if (measure1 + measure2 < 0) {
	    name = "(-)" + name;
	    size *= 1;
	  }
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

	  int product_size {measure_operand (operand1) * measure_operand (operand2)};
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
	
	[[fallthrough]];
	
      case '/':
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
      for (xml_node child : expression.children ()) {
	Expression *handler {formula->operand_handlers[child.name ()]};
	std::string element {(*handler) (child, formula)};
	if (element == "")
	  { return element; }
	elements.insert (element);
      }

      int var {formula->next_var};
      std::string set_name {"{"};
      auto el_iter {elements.begin ()};
      set_name += *el_iter;
      formula->make_clause ({var});
    
      for (++el_iter; el_iter != elements.end (); ++el_iter) {
	set_name += "," + *el_iter;
	formula->make_clause ({++var});
      }
      set_name += "}";
    
      if (!formula->sets.contains (set_name)) 
	{ formula->next_var = var + 1; }
      else [[likely]] 
	{ formula->construct_new_set (set_name, elements.size ()); }

      return set_name;
    }

    return "";
  }
};
    
struct EmptySet : public Expression {
  inline std::string operator () (xml_node, Formula *formula) {
    if (!formula->sets.contains ("{}")) {
      int var {formula->next_var++};
      formula->sets["{}"] = {var, 1};
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
	formula->sets["TRUE"] = {var, 1};
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
      std::string dom {"dom(" + definiendum + ")}"};
      std::string ran {"ran(" + definiendum + ")}"};
      if (!formula->sets.contains (dom))
	{ formula->construct_new_set (dom, formula->sets[rhs_dom][1]); }
      if (!formula->sets.contains (ran))
	{ formula->construct_new_set (ran, formula->sets[rhs_ran][1]); }

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
      non_empty_func (formula->sets[operand1][0], formula->sets[operand1][1], binding_var);
      return binding_var;
    }

    if (!formula->predefined_literals.contains (operand2)) {
      if (operand2.substr (0, std::string {"FIN("}.length ()) == "FIN(")
	{}
      else
	{ non_empty_func (formula->sets[operand2][0], formula->sets[operand2][1], binding_var); }
    }

    return binding_var;
  }
};

struct Equality : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    // Currently only works for comparing integers although the operator is overloaded in Atelier B.
    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }

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
    return formula->next_var++;
  }
};

struct Surjection : public Relational {
  inline int operator () (xml_node relation, Formula *formula) {
    GreaterEqual ge;
    return ge (relation, formula);
  }
};

struct SetOfRelations : public Relational {
  inline int operator () (xml_node relation, Formula *formula) {
    NotCompared nc;
    return nc (relation, formula);
  }
};

struct TotalInjection : public Relational {
  inline int operator () (xml_node relation, Formula *formula) {
    LessEqual le;
    return le (relation, formula);
  }
};

struct Bijection : public Relational {
  inline int operator () (xml_node relation, Formula *formula) {
    Equality eq;
    return eq (relation, formula);
  }
};

struct Set : public Definition {
  inline int operator () (xml_node set, Formula *formula) {
    // Only POW (Z) || Z
    if (set.child ("Id").attribute ("typref").as_int () > INTEGER)
      { return -1; }
  
    std::string id {set.child ("Id").attribute ("value").value ()};

    int var {formula->next_var};

    auto fresh_construct {
      [formula, &id, var] (int size) {
	formula->construct_new_set (id, size);
	std::vector<int> vec (size);
	std::iota (vec.begin (), vec.end (), var);
	return vec;
      }};
    
    if (set.child ("Enumerated_Values")) {
      int size = 0;
      for (auto el : set.child ("Enumerated_Values").children ())
	{ ++size; } 
     formula->make_clause (fresh_construct (size), size);
    }
    else
      { formula->make_clause (fresh_construct (formula->upper_bound)); }

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
  inline int operator () (xml_node comparison, Formula *formula) {
    std::string op {comparison.attribute ("op").value ()};
    if (!formula->comparison_handlers.contains (op))
      { return -1; }

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
  
Formula::Formula (int k, std::string pbs_name) 
  : upper_bound {k}, pbs_name {pbs_name},
    predefined_literals {"MAXINT", "MININT", "TRUE"
			 "NAT", "NAT1", "INT"} {
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
}
 
inline void Formula::construct_new_set (std::string &name, int size) {
  int var {next_var};
  sets[name] = {var, size};
  next_var = var + size;
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

void Formula::explore_context (xml_node proof_obligations) {
  for (xml_node definition : proof_obligations.children ()) {
    std::string name {definition.attribute ("name").value ()};
    if (std::string {"Define"} == definition.name ()
	&& (name == "ctx"                                        
	    // || name == "sets"                                    
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
	    abort ();
	  }
	}
	else
	  { std::cerr << interior.name () << '\n'; }
      }
    }}
}

void Formula::make_clause (std::vector<int> &&literals, int degree, std::string comparison) {
  int size {0};
  
  if (comparison == "=")
    { ++nbequals; }
  for (auto lit : literals) {
    ++size;
    if (lit < 0) {
      pbs_body << "-1 x";
      --degree;
      lit *= -1;
    }
    else
      { pbs_body << "+1 x"; }
    pbs_body << lit << ' ';
  }
  pbs_body << comparison << ' ' << degree << ";\n";
  ++nbclauses;

  update_intsize (size + abs (degree));
}

void Formula::make_clause (std::vector<int> &&W, std::vector<std::string> &&X, int K, std::string comparison) {
  int size {0};

  if (comparison == "=")
    { ++nbequals; }
  for (int i {0}; i < W.size (); ++i) {
    int max {sets[X[i]][1]};
    int x {sets[X[i]][0]};
    int coeff {W[i]};
    
    for (int j {0}; j < max; ++j) {
      if (coeff >= 0) {
	pbs_body << '+';
	size += coeff;
      }
      else
	{ size += -coeff; }
      
      pbs_body << coeff << " x" << x + j << ' ';
    }
  }

  pbs_body << comparison << ' ' << K << ";\n";
  ++nbclauses;

  update_intsize (size + abs (K));
}
			   
int main (int argc, char **argv) {
  int k {atoi (argv[1])};
  std::string out_file {get_pbs_file_name (argv[2])};

  auto t1 {std::chrono::system_clock::now ()};

  Formula *formula {new Formula {k, out_file}};

  pugi::xml_document doc;
  doc.load_file (argv[2]);

  formula->explore_context (doc.first_child ());
  formula->print_pbs ();

  #ifdef AUX_MESSAGE
  formula->list_aux ();
  formula->list_sets ();
  #endif

  delete formula;
  
  auto t2 {std::chrono::system_clock::now ()};
  std::clog << (std::chrono::duration_cast<std::chrono::milliseconds> (t2 - t1)) << '\n';
  
  return 0;
}
