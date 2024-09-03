/*
 * set-sizing-for-counter-models
 * Copyright (C) 2024 Univ. Artois & CNRS
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or (at your
 * option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with the program.
 * If not, see http://www.gnu.org.licenses.
 */

#include "../include/solution_to_pog.hpp"
#include "utils/clock.hpp"
#include "pugixml.hpp"

#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>

std::string get_line (const char *filename, char first_char) {
  std::ifstream solver_output {filename};
  std::string line;
  while (!solver_output.eof ()) {
    getline (solver_output, line);
    if (line[0] == first_char)
      { break; }
  }
  return line;
}

void get_abs_set_sizes (std::map<std::string, int> &set_sizes,
			std::ifstream &abs_sets,
			std::string &model) {
  std::string set_name;
  while (abs_sets >> set_name) {
    int start, size, sign_unused;
    abs_sets >> start >> size >> sign_unused;
    int end {start + size - 1};

    std::stringstream variables {model};
    std::string var;

    int count {0};
    variables >> var; // 'v'
    while (variables >> var) {
      int current {std::stoi (var.substr (var.find ('x') + 1))};
      if (current > end)
	{ break; }
      else if (current < start)
	{ continue; }

      if (var[0] == '-')
	{ continue; }
      ++count;
    }

    set_sizes[set_name] = count;
  }
}

int get_typref (pugi::xml_document &doc, int outer_typref) {
  std::stringstream outer_stream;
  pugi::xml_node &&type_infos {doc.first_child ().child ("TypeInfos")};
  
  for (auto &node : type_infos.children ()) {
    if (node.attribute ("id").as_int () == outer_typref) {
      node.child ("Unary_Exp").first_child ().print (outer_stream);
      break;
    }
  }

  for (auto &node : type_infos.children ()) {
    std::stringstream inner_stream;
    node.first_child ().print (inner_stream);
    if (inner_stream.str () == outer_stream.str ())
      { return node.attribute ("id").as_int (); }
  }

  int greatest {};
  for (auto &node : type_infos.children ()) {
    int current {node.attribute ("id").as_int ()};
    if (current > greatest)
      { greatest = current; }
  }
  return ++greatest;
}
        
void replace_abstract (pugi::xml_document &doc,
		       std::map<std::string, int> &set_sizes) {
  auto replace_abs_sets
    { [&doc, &set_sizes] (pugi::xml_node &set) {
	std::string name {set.child ("Id").attribute ("value").value ()};
	if (set_sizes.contains (name)) {
	  int typref {get_typref (doc,
				  set.child ("Id").attribute ("typref").as_int ())}; 
	  pugi::xml_node enum_val {set.append_child ("Enumerated_Values")};
	  for (int i {0}; i < set_sizes[name]; ++i) {
	    pugi::xml_node element {enum_val.append_child ("Id")};
	    std::string value {name + "e" + std::to_string (i)};
	    element.append_attribute ("value") = value.c_str ();
	    element.append_attribute ("typref") = std::to_string (typref).c_str ();
	  }
	}
      }};
	    
  auto find_and_replace_sets
    { [&replace_abs_sets] (pugi::xml_node &define) {
	for (auto &child : define.children ("Set"))
	  { replace_abs_sets (child); }
      }};

  for (auto &define : doc.first_child ().children ("Define"))
    { find_and_replace_sets (define); }
}

namespace SOLUTION_TO_POG {
  bool run (const char *solver_output, const char *abstract_sets, std::string output_dir) {
    std::string model {get_line (solver_output, 'v')};
    if (model.empty ()) {
      std::string state {get_line (solver_output, 's')};
      std::cout << "No model found.\n";
      std::cout << state << '\n';
      return false;
    }

    std::ifstream abs_sets {abstract_sets};
    std::string pog_name;
    getline (abs_sets, pog_name);

    std::map<std::string, int> set_sizes;
    get_abs_set_sizes (set_sizes, abs_sets, model);

    pugi::xml_document doc;
    doc.load_file (pog_name.c_str ());

    replace_abstract (doc, set_sizes);

    std::filesystem::path old_pog {pog_name};
    std::filesystem::path new_pog {output_dir};
    std::string output_pog {new_pog.string () + '/'
			    + old_pog.stem ().string ()
			    + "_concrete.pog"};

    doc.save_file (output_pog.c_str ());
    return true;
  }
}

// int main (int argc, char **argv) {
//   RunClock *run_clock {new RunClock {}};

//   if (argc < 3) {
//     std::cerr << "Usage: ./solution_to_pog <solver_output> <abstract_sets> [<pog_output_dir>]\n";
//     return 1;
//   }

//   std::string output_dir {"."};
//   if (argc == 4)
//     { output_dir = argv[3]; }

//   if (!SOLUTION_TO_POG::run (argv[1], argv[2], output_dir)) {
//     std::cerr << "To POG failed.\n";
//     return 1;
//   }
    
//   std::cout << "To POG: ";
//   delete run_clock;
//   return 0;
// }
