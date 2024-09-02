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
