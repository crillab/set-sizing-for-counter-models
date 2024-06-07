#include "pugixml.hpp"

#include <algorithm>
#include <array>
#include <chrono>
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

class Formula {
  std::map<std::string, std::array<int, 2>> sets;    // <"name", {first_var, size}
  std::map<std::string, Definition *> comparison_handlers;
  std::map<std::string, Definition *> definition_handlers;
  std::map<std::string, Expression *> operand_handlers;
  std::set<std::string> predefined_literals;
  std::stringstream pbs_body;
  std::string pbs_name;
  int next_var {1}, nbclauses {0};
  int upper_bound {};

  inline int complement (int);
  inline int constrain_equality (std::string &, std::string &);
  inline int constrain_gte (std::string &, std::string &);
  inline void construct_new_set (std::string &, int);
  inline void make_clause (std::vector<int> &&, int = 1, std::string = ">=");
  
public:
  Formula (int, std::string);
  ~Formula ();
  inline void explore_context (xml_node);

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
  
  friend struct Set;
  friend struct BinaryPred;
  friend struct ExpComparison;
  friend struct UnaryPred;
  friend struct NaryPred;

  friend struct UnaryExp;
  friend struct EmptySet;
  friend struct Id;

  friend class SetSizer;
  
  // spot-check interface
  int get_next_var () {
    return next_var;
  }
  void print_pbs () {
    std::cout << pbs_body.str ();
  }
  int predicates {0};
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
  Formula *formula;
  int degree;
  int selector;

  int get_limits (std::vector<std::string> &V) {
    return std::accumulate (V.begin (), V.end (), 0,
			    [this] (int acc, std::string &name)
			    { return acc + formula->sets[name][1]; });
  }
			     
  void run_through (std::vector<std::string> &V, char sign) {
    for (auto &el_of_v : V) {
      int var {formula->sets[el_of_v][0]};
      for (int i {0}; i < formula->sets[el_of_v][1]; ++i)
	{ formula->pbs_body << sign << "1 x" << var++ << ' '; }
    }
  }
	
  inline void if_var (std::vector<std::string> &positives,
		      std::vector<std::string> &negatives) {
    // M := -α + |pos|

    int positive_limits {get_limits (positives)};
    int M {degree - positive_limits};
    if (M > 0)
      { formula->pbs_body << '+' << M; }
    else
      { formula->pbs_body << M; }
    formula->pbs_body << " x" << selector << ' ';

    run_through (negatives, '+');
    run_through (positives, '-');

    formula->pbs_body << ">= " << -positive_limits << ";\n";
  }

  inline void if_pbexpr (std::vector<std::string> &positives,
			 std::vector<std::string> &negatives) {
    // M := -(|neg| + α + 2)

    run_through (positives, '+');
    run_through (negatives, '-');

    int negative_limits {get_limits (negatives)};
    int M {-(negative_limits + degree + 2)};
    if (M > 0)
      { formula->pbs_body << '+' << M; }
    else
      { formula->pbs_body << M; }
    formula->pbs_body << " x" << selector
		      << " >= " << degree + 1 << ";\n";
  }

public:
  SetSizer (Formula *formula) : formula {formula} {}
  
  inline int operator () (std::vector<std::string> positives,
			  std::vector<std::string> negatives,
			  int alpha) {
    // Always of the the form Σpos - Σneg <= α
    // Returns selector variable

    selector = formula->next_var++;
    degree = alpha;

    if_var (positives, negatives);
    if_pbexpr (positives, negatives);

    return selector;
  }
};

struct Expression {
  virtual std::string operator () (xml_node, Formula *) = 0;
};

struct Id : public Expression {
  inline std::string operator () (xml_node operand, Formula *formula) {
    std::string value {operand.attribute ("value").value ()};
    if (!formula->predefined_literals.contains (value) && !formula->sets.contains (value)) 
      { formula->construct_new_set (value, formula->upper_bound); }

    return value;
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

struct ElementOf : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }

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

    int binding_var {formula->next_var++}, strictly_pos {}, non_empty_flag {};
    
    if (operand2 == "NAT1") {
      strictly_pos = formula->next_var++;
      non_empty_func (formula->sets[operand1][0], formula->sets[operand1][1], strictly_pos);
    }

    if (!formula->predefined_literals.contains (operand2)) {
      if (operand2.substr (0, std::string {"FIN("}.length ()) == "FIN(")
	{}
      else if (strictly_pos > 0) {
	non_empty_flag = formula->next_var++;
	non_empty_func (formula->sets[operand2][0], formula->sets[operand2][1], non_empty_flag);
	formula->make_clause ({binding_var, -strictly_pos, -non_empty_flag});
	for (int conjunct : {strictly_pos, non_empty_flag})
	  { formula->make_clause ({-binding_var, conjunct}); }
      }
      else
	{ non_empty_func (formula->sets[operand2][0], formula->sets[operand2][1], binding_var); }
    }

    return binding_var;
  }
};

struct Equality : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }

    SetSizer set_sizer {formula};
    int forwards {set_sizer ({operand1}, {operand2}, 0)};
    int backwards {set_sizer ({operand2}, {operand1}, 0)};

    int equality {formula->next_var++};
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
    return set_sizer ({operand1}, {operand2}, 0);
  }
};

struct GreaterThan : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }

    SetSizer set_sizer {formula};
    return set_sizer ({operand1}, {operand2}, 1);
  }
};

struct LessThan : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }

    SetSizer set_sizer {formula};
    return set_sizer ({operand2}, {operand1}, 1);
  }
};

struct LessEqual : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    get_operands (comparison, formula);
    if (operand2.empty ())
      { return -1; }

    SetSizer set_sizer {formula};
    return set_sizer ({operand2}, {operand1}, 0);
  }
};

struct NotCompared : public Comparison {
  inline int operator () (xml_node comparison, Formula *formula) {
    return formula->next_var++;
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
      formula->make_clause (fresh_construct (size), size, "=");
    }
    else
      { formula->make_clause (fresh_construct (formula->upper_bound)); }

    return var;
  }
};
  
struct PredGroup : public Definition {
protected:
  inline bool skip_test (xml_node predicate) {
    bool skip
      {
	false && (
	// Deal with only POW (Z) and Z
	std::ranges::any_of (predicate.children (),
			     [] (auto child) { return child.attribute ("typref").as_int () > INTEGER; }) ||
	// Need some sets
	std::ranges::all_of (predicate.children (),
			     [] (auto child) { return child.attribute ("typref").as_int () == INTEGER; }) ||
	// Skip x = min (x)..max (x)
	convexity_constraint (predicate))
      };
    return skip;
  }
};

struct BinaryPred : public PredGroup {
  inline int operator () (xml_node predicate, Formula *formula) {
    if (skip_test (predicate) ||
	std::ranges::any_of (predicate.children (),
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
    
    int binary_pred {formula->next_var++};
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
    if (skip_test (comparison))
      { return -1; }

    std::string op {comparison.attribute ("op").value ()};
    if (!formula->comparison_handlers.contains (op))
      { return -1; }

    Definition *handler {formula->comparison_handlers[op]};
    return (*handler) (comparison, formula);
  }
};

struct UnaryPred : public PredGroup {
  inline int operator () (xml_node predicate, Formula *formula) {
    if (skip_test (predicate))
      { return -1; }

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
    if (skip_test (predicate) ||
	std::ranges::any_of (predicate.children (),
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

    int junction_var {formula->next_var++};
    
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
  
  definition_handlers["Set"] = new Set {};
  definition_handlers["Binary_Pred"] = new BinaryPred {};
  definition_handlers["Exp_Comparison"] = new ExpComparison {};
  definition_handlers["Unary_Pred"] = new UnaryPred {};
  definition_handlers["Nary_Pred"] = new NaryPred {};

  operand_handlers["Unary_Exp"] = new UnaryExp {};
  operand_handlers["EmptySet"] = new EmptySet {};
  operand_handlers["Id"] = new Id {};
}

Formula::~Formula () {
  for (auto &map : {comparison_handlers, definition_handlers}) {
    for (auto &couple : map)
      { delete couple.second; }
  }

  for (auto &couple : operand_handlers)
    { delete couple.second; }
}
 
inline void Formula::construct_new_set (std::string &name, int size) {
  int var {next_var};
  sets[name] = {var, size};
  next_var = var + size + 1;
}

int Formula::complement (int negandum) {
  int aux {next_var++};

  make_clause ({-aux, negandum}, 1, "=");

  return aux;
}

// int Formula::constrain_equality (std::string &op1, std::string &op2) { // MIGHT CHANGE
//   std::array<int, 2> operand1 {sets[op1]};
//   std::array<int, 2> operand2 {sets[op2]};
//   int max {operand1[1] < operand2[1] ? operand1[1] : operand2[1]}; // Only up to the size of the smaller one.

//   int aux {next_var++};
  
//   for (int i {0}; i <= max; ++i) {
//     for (int aux_sign : {-1, 1}) {
//       for (int var_sign : {-1, 1})
// 	{ make_clause ({aux_sign * aux, var_sign * (operand1[0] + i), -var_sign * (operand2[0])}); }
//     }
//   }

//   return aux;
// }

// int Formula::constrain_gte (std::string &op1, std::string &op2) {
//   std::array<int, 2> operand1 {sets[op1]};
//   std::array<int, 2> operand2 {sets[op2]};
//   int max {operand1[1] < operand2[1] ? operand1[1] : operand2[1]};

//   int aux {next_var++};

//   for (int i {0}; i <= max; ++i)
//     { make_clause ({-(operand1[0] + i), operand2[0] + i}); }

//   return aux;
// }

void Formula::explore_context (xml_node proof_obligations) {
  for (xml_node definition : proof_obligations.children ()) {
    std::string name {definition.attribute ("name").value ()};
    if (std::string {"Define"} == definition.name ()
	&& (name == "ctx"                                        
	    || name == "sets"                                    
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
	    interior.print (std::cout);
	    abort ();
	  }
	}
	else
	  { std::cout << interior.name () << '\n'; }
      }
    }}
}

void Formula::make_clause (std::vector<int> &&literals, int degree, std::string comparison) {
  for (auto lit : literals) {
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
}

int main (int argc, char **argv) {
  int k {atoi (argv[1])};
  std::string out_file {get_pbs_file_name (argv[2])};

  auto t1 {std::chrono::system_clock::now ()};

  Formula formula {k, out_file};

  pugi::xml_document doc;
  doc.load_file (argv[2]);

  formula.explore_context (doc.first_child ());
  formula.print_pbs ();

  auto t2 {std::chrono::system_clock::now ()};
  // std::cout << (std::chrono::duration_cast<std::chrono::milliseconds> (t2 - t1)) << '\n';
  
  return 0;
}
