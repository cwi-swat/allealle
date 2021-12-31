module benchmark::relational::AlleAlleBenchmarkSuite

import benchmark::relational::account::AlleAlleAccountBenchmark;
import benchmark::relational::filesystem::AlleAlleFileSystemBenchmark;
import benchmark::relational::handshake::AlleAlleHandshakeBenchmark;
import benchmark::relational::pigeonhole::AlleAllePigeonholeBenchmark;
//import benchmark::relational::ringelection::AlleAlleRingElectionBenchmark;
import benchmark::relational::rivercrossing::AlleAlleRiverCrossingBenchmark;
import benchmark::relational::square::AlleAlleSquareBenchmark;

import benchmark::relational::rebel2::hanoi::HanoiBenchmark;
import benchmark::relational::rebel2::debitcard::DebitCardBenchmark;

void runAllBenchmarks(str postfix = "") {
  runAccountBenchmark(postfix = postfix);
  runFileSystemBenchmark(postfix = postfix);
  runHandshakeBenchmark(postfix = postfix);
  runPigeonholeBenchmark(postfix = postfix);
  //runRingElectionBenchmark(postfix = postfix);
  runRiverCrossingBenchmark(postfix = postfix);
  runSquareBenchmark(postfix = postfix);
  
  runHanoiBenchmark(postfix = postfix);
  runDebitCardBenchmark(postfix = postfix);
}
