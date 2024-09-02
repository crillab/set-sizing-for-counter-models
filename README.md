# set-sizing-for-counter-models
## Building
- Before running ``make``, a pseudo-Boolean solver and [pugixml](https://github.com/zeux/pugixml/tree/master/src) are necessary.
- In Makefile, three variables must be correctly set in order for this tool to work.
  - PUGIXML_SRC must be set to the location of the file pugixml.cpp.
  - PUGIXML_LIB must be set to the directory containing the other two source files of pugixml.
  - PB_SOLVER must be set to the command for running the chosen pseudo-Boolean solver, or to the path to its executable.

## Usage
- As inputs, the path to a POG file and the positive, natural upper-bound for searching for set sizes must be given as arguments.
- As outputs, if possible, there will be four files named according to the stem of the input POG.
  - `<stem>.abs_out` lists the originally abstract sets followed immediately and most interestingly by the first propositional variable that represents one of its elements. Its elements' variables are contiguous.
  - `<stem>_concrete.pog` is the new POG file instantiating the abstract sets of the input.
  - `<stem>.pbo` is the pseudo-Boolean problem instance encoding the original POG file.
  - `<stem>.pb_solver_out` has the output of the pseudo-Boolean solver piped into it.

### Run
- ./set-sizing-for-counter-models -i `<input POG>` -k `<upper-bound on set size>`

## Licensing

This software has been developed for the project BLaSST. It is released under the terms of the GNU LGPL v3.0 license.

BLaSST is a project funded by ANR, the French research agency. It involves the VeriDis team of Inria in Nancy, the CRIL laboratory of University of Artois in Lens, the CLEARSY company, and the Montefiore Institute of University of Liège in Belgium. BLaSST was selected for funding as project ANR-21-CE25-0010.