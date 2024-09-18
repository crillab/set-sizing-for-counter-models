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

#ifndef XML_TO_SOLVER_H
#define XML_TO_SOLVER_H

namespace XML_TO_SOLVER {
  bool run (const char *input_pog_file, int k, bool optimization, bool stop_for_big);
}

#endif
