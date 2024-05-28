#include "pugixml.hpp"

#include <algorithm>
#include <array>
#include <chrono>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <vector>

using xml_node = const pugi::xml_node &;

static int k; // upper-bound for size of abstract sets

enum typref { POW_INTEGER, INTEGER };

struct Definition;
struct Set;
struct PredGroup;
struct ExpComparison;
struct UnaryPred;

class Formula {
  std::map<std::string, std::array<int, 2>> sets;    // <"name", {start_var, max_size}>
  std::map<std::string, Definition *> definition_handlers {};
  std::stringstream cnf_body;
  std::string cnf_name;
  int nbvar {0}, nbclauses {0};
  int next_var {1};
  int upper_bound;

  inline void make_clause (std::vector<int> &&);
  inline void order_encode_range (int, int);
  
public:
  Formula (int, std::string);
  ~Formula ();
  inline void apply_order_encoding (bool = true);
  inline void explore_context (xml_node);
  friend struct Set;
  friend struct ExpComparison;
  friend struct UnaryPred;

  int get_next_var () {
    return next_var;
  }
  void print_cnf () {
    std::cout << cnf_body.str ();
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
  
std::string get_cnf_file_name (char *pog_name) {
  std::string read_in_file {pog_name};
  read_in_file = read_in_file.substr (read_in_file.rfind ('/', read_in_file.rfind ('/') - 1) + 1);
  std::ranges::replace (read_in_file, '/', '-');
  read_in_file.replace (read_in_file.rfind ("pog"), 3, "cnf");
  return read_in_file;
}

struct Definition {
  virtual int operator () (xml_node, Formula *) = 0;
};

struct Set : public Definition {
  inline int operator () (xml_node set, Formula *formula) {
    // Only POW (Z)
    if (set.child ("Id").attribute ("typref").as_int () != 0)
      { return -1; }
  
    std::string id {set.child ("Id").attribute ("value").value ()};

    int size {formula->upper_bound};
    int var {formula->next_var};
    
    if (set.child ("Enumerated_Values")) {
      size = 0;
      for (auto el : set.child ("Enumerated_Values").children ())
	{ ++size; }
      formula->make_clause ({var + size});
      formula->make_clause ({-(var + size - 1)});
    }

    formula->sets[id] = {var, size}; // next_var <=> |set|_{\lte 0}
    var += size;
    formula->next_var = var + 1;

    return var;
  }
};

struct PredGroup : public Definition {
  inline bool skip_test (xml_node predicate) {
    bool skip
      {
	// Deal with only POW (Z) and Z
	std::ranges::any_of (predicate.children (),
			     [] (auto child) { return child.attribute ("typref").as_int () > INTEGER; }) ||
	// Need some sets
	std::ranges::all_of (predicate.children (),
			     [] (auto child) { return child.attribute ("typref").as_int () == INTEGER; }) ||
	// Skip x = min (x)..max (x)
	convexity_constraint (predicate)
      };
    return skip;
  }
};

struct ExpComparison : public PredGroup {
  inline int operator () (xml_node comparison, Formula *formula) {
    if (skip_test (comparison))
      { return -1; }

    ++(formula->predicates);
    return 0;
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

    int negation {(formula->next_var)++};
    for (int sign : {1, -1})
      { formula->make_clause ({negandum * sign, negation * sign}); }

    return negation;
  }
};

Formula::Formula (int k, std::string cnf_name) 
  : upper_bound {k}, cnf_name {cnf_name} {
  definition_handlers["Set"] = new Set {};
  definition_handlers["Exp_Comparison"] = new ExpComparison {};
  definition_handlers["Unary_Pred"] = new UnaryPred {};
}

Formula::~Formula () {
  for (auto couple : definition_handlers)
    { delete couple.second; }
}

void Formula::apply_order_encoding (bool non_empty) {
  for (auto &set : sets) {
    int zero {set.second[0]};
    int size {set.second[1]};

    order_encode_range (zero, size);
    make_clause ({zero + size});
    if (non_empty)
      { make_clause ({-zero}); }
  }
}

void Formula::explore_context (xml_node proof_obligations) {
  std::ranges::for_each (proof_obligations.children (),
			 [this] (auto definition) {
			   std::string name {definition.attribute ("name").value ()};
			   if (std::string {"Define"} == definition.name ()
			       && (name == "ctx"                                        // CHECK // Different from POGParser
				   // || name == "ass"                                  // CHECK
				   || name == "sets"                                    // CHECK
				   || name.substr (name.length () - 3) == "prp")) {
			     for (xml_node interior : definition.children ()) {
			       if (definition_handlers.contains (interior.name ())) {
				   Definition *handler {definition_handlers[interior.name ()]};
				   (*handler) (interior, this);
			       }
			       else
				 { std::cout << interior.name () << '\n'; }
			     }
			   }});
}

void Formula::make_clause (std::vector<int> &&literals) {
  for (auto lit : literals)
    { cnf_body << lit << ' '; }
  cnf_body << '0' << std::endl; // "0\n";
}

void Formula::order_encode_range (int zero, int size) {
  for (int i {0}; i < size - 1; ++i)
    { make_clause ({-(zero + i), zero + i + 1}); }
}

int main (int argc, char **argv) {
  k = atoi (argv[1]);
  std::string out_file {get_cnf_file_name (argv[2])};

  auto t1 {std::chrono::system_clock::now ()};

  Formula formula {k, out_file};

  pugi::xml_document doc;
  doc.load_file (argv[2]);

  formula.explore_context (doc.first_child ());
  formula.apply_order_encoding ();

  auto t2 {std::chrono::system_clock::now ()};
  std::cout << (std::chrono::duration_cast<std::chrono::milliseconds> (t2 - t1)) << '\n';
  
  return 0;
}
