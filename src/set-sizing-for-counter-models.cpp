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
#include "../include/xml_to_solver.hpp"
#include "utils/clock.hpp"

#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <sstream>
#include <string>

int main (int argc, char **argv) {
  std::string help {"Usage: ./set-sizing-for-counter-models "
		    "-i <input POG> -k <upper-bound on set sizes as positive nat>\n"};
  
  std::string input;
  int k;
  bool k_set {};

  for (int i {1}; i < argc; ++i) {
    auto get_option_val { [argc, &argv] (int &i)
    { return ++i < argc ? argv[i] : ""; }};
    
    if (std::string {"-i"} == argv[i]) 
      { input = get_option_val (i); }
    else if (std::string {"-k"} == argv[i]) {
      try
	{ k = std::atoi (get_option_val (i)); }
      catch (...) {
	std::cerr << help;
	return 1;
      }
      if (k > 0)
	{ k_set = true; }
    }
  }
  
  if (input.empty () || !k_set) {
    std::cerr << help;
    return 1;
  }

  auto get_stem
    { [&input] {
      std::filesystem::path in {input};
      return in.stem ().string ();
    }};

  RunClock *clock {new RunClock {}};
  
  if (!XML_TO_SOLVER::run (input.c_str (), k, true)) {
    std::cerr << "\nFailed to encode to pseudo-Boolean problem instance.\n";
    return 1;
  }
  std::cout << "To PBO: ";
  delete clock;

  std::string call_pb_solver {PB_SOLVER};
  call_pb_solver += ' ' + get_stem () + ".pbo > " + get_stem () + ".pb_solver_out";
  clock = new RunClock {};
  system (call_pb_solver.c_str ());
  std::cout << "Solver: ";
  delete clock;

  std::string solver_output {get_stem () + ".pb_solver_out"};
  std::string abstract_sets {get_stem () + ".abs_out"};

  clock = new RunClock {};
  if (!SOLUTION_TO_POG::run (solver_output.c_str (), abstract_sets.c_str ())) {
    std::cerr << "\nFailed to generate new POG file.\n";
    return 1;
  }
  std::cout << "To POG: ";
  delete clock;

  return 0;
}
