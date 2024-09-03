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

#ifndef CLOCK_H
#define CLOCK_H

#include <chrono>

class RunClock {
  std::chrono::time_point<std::chrono::system_clock> t1;

public:
  RunClock ();
  ~RunClock ();
};

#endif
