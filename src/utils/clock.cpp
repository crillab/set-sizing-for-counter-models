#include "clock.hpp"

#include <iostream>

RunClock::RunClock ()
  : t1 {std::chrono::system_clock::now ()} {}

RunClock::~RunClock () {
  auto t2 {std::chrono::system_clock::now ()};
  std::cout << (std::chrono::duration_cast<std::chrono::milliseconds> (t2 - t1)).count () << "ms\n";
}
