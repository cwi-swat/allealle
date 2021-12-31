module benchmark::relational::rebel2::debitcard::DebitCardBenchmark

extend benchmark::AlleAlleBenchmark;

import IO;

void runDebitCardBenchmark(str postfix = "") 
  = runBenchmark([3,5], "rebel2", "debitcard", true, postfix = postfix); 

str constructRels(int config) = readFile(|project://allealle/src/benchmark/relational/rebel2/debitcard| + "rel_<config>_steps.allepart");
str getConstraints(int config) = readFile(|project://allealle/src/benchmark/relational/rebel2/debitcard/constraints.allepart|);