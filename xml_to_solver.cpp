#include "pugixml.hpp"

#include <algorithm>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <vector>

using xml_node = const pugi::xml_node &;

static int k; // upper-bound for size of abstract sets

class Formula {
  std::map<std::string, int *> sets;    // <"name", {start_var, max_size}>
  std::stringstream cnf_body;
  std::string cnf_name;
  int nbvar {0}, nbclauses {0};
  int next_var {1};
  int upper_bound;

  inline void handle_predicate (xml_node);
  inline void handle_set (xml_node);
  void make_clause (std::vector<int> literals) {
    for (auto lit : literals)
      { cnf_body << literal << ' '; }
    std::cout << "0\n";
  }

public:
  Formula (int k, std::string cnf_name)
    : upper_bound {k}, cnf_name {cnf_name} {}
  inline void explore_context (xml_node);
};

void Formula::explore_context (xml_node proof_obligations) {
  std::ranges::for_each (proof_obligations.children (),
			 [this] (auto definition) {
			   std::string name {definition.attribute ("name").value ()};
			   if (std::string {"Define"} == definition.name ()
			       && (name == "ctx"                                        // CHECK
				   || name == "ass"
				   || name == "sets"                                    // CHECK
				   || name.substr (name.length () - 3) == "prp")) {
			     xml_node interior {definition.first_child ()};
			     if (std::string {"Set"} == interior.name ())
			       { handle_set (interior); }
			     else
			       { handle_predicate (interior); }
			   }});
}

void handle_set (xml_node set) {
  std::string id {set.child ("Id").value ()};

  int size {upper_bound};
  if (set.child ("Enumerated_Values")) {
    size = 0;
    for (auto el : set.child ("Enumerated_Values").children ())
      { ++size; }
    make_clause ({next_var + size - 1});
    make_clause ({-(next_var + size - 2)});
  }

  sets[id] = {next_var, size};
  next_var += size;
}
    

std::string get_cnf_file_name (char *pog_name) {
  std::string read_in_file {pog_name};
  read_in_file = read_in_file.substr (read_in_file.rfind ('/', read_in_file.rfind ('/') - 1) + 1);
  std::ranges::replace (read_in_file, '/', '-');
  read_in_file.replace (read_in_file.rfind ("pog"), 3, "cnf");
  return read_in_file;
}

int main (int argc, char **argv) {
  k = atoi (argv[1]);
  std::string out_file {get_cnf_file_name (argv[2])};

  Formula formula {k, out_file};

  pugi::xml_document doc;
  doc.load_file (argv[2]);

  formula.explore_context (doc.first_child ());
  
  return 0;
}
