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

#include "clock.hpp"

#include <iostream>

RunClock::RunClock ()
  : t1 {std::chrono::system_clock::now ()} {}

RunClock::~RunClock () {
  auto t2 {std::chrono::system_clock::now ()};
  std::cout << (std::chrono::duration_cast<std::chrono::milliseconds> (t2 - t1)).count () << "ms\n";
}
