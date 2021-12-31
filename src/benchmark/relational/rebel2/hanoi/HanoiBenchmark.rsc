module benchmark::relational::rebel2::hanoi::HanoiBenchmark

extend benchmark::AlleAlleBenchmark;

import IO;

void runHanoiBenchmark(str postfix = "") 
  = runBenchmark([3,4,5], "rebel2", "hanoi", true, postfix = postfix); 

str constructRels(int config) = readFile(|project://allealle/src/benchmark/relational/rebel2/hanoi| + "rel_<config>_discs.allepart");
str getConstraints(int config) = readFile(|project://allealle/src/benchmark/relational/rebel2/hanoi/constraints.allepart|);