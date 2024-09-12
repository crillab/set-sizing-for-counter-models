STANDARD := -std=c++20

PUGIXML_SRC := src/pugi/pugixml.cpp
PUGIXML_LIB := src/pugi

PB_SOLVER_PREFIX := "../../exact/build/Exact\ --print-sol"

all: set-sizing-for-counter-models

set-sizing-for-counter-models: 
	g++ $(STANDARD) -I $(PUGIXML_LIB) -D"PB_SOLVER=\"$(PB_SOLVER_PREFIX)\"" -O3 -o set-sizing-for-counter-models src/set-sizing-for-counter-models.cpp src/xml_to_solver.cpp src/solution_to_pog.cpp src/utils/clock.cpp $(PUGIXML_SRC)

clean: clear_results
	rm set-sizing-for-counter-models 

clear_results:
	rm *_out *_concrete.pog *.pbo
