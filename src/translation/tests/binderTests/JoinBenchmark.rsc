module translation::tests::binderTests::JoinBenchmark

extend translation::tests::binderTests::TesterBase;

import util::Benchmark;

RelationMatrix constructPigeonRelation(int nrOfPigeons) = truths([["p<i>"] | int i <- [1..nrOfPigeons+1]]);
RelationMatrix constructHoleRelation(int nrOfHoles) = truths([["h<i>"] | int i <- [1..nrOfHoles+1]]);
RelationMatrix constructNestRelation(RelationMatrix pigeons, RelationMatrix holes) = vars([[p,h] | [str p] <- pigeons, [str h] <- holes], "nest");

void runJoinBenchmark(int nrOfPigeons, int nrOfHoles, int warmup, int nrOfRounds) {
  println("Preparing \'dot join\' benchmark for <nrOfPigeons> pigeons and <nrOfHoles> holes");

  pigeons = constructPigeonRelation(nrOfPigeons);
  holes = constructHoleRelation(nrOfHoles);
  nest = constructNestRelation(pigeons, holes);
 
  print("Warming up (<warmup> rounds): ");
  for (int i <- [0..warmup]) {
    r = dotJoin(pigeons,nest);
    print(".");
  }
  print("done\n");
  
  list[int] times = [];
  
  print("Running benchmark (<nrOfRounds> total iterations): ");
  for (int i <- [0..nrOfRounds]) {
    for (Index idx <- pigeons) {
      RelationMatrix p = (idx : pigeons[idx]);
      int startTime = cpuTime();
      r = dotJoin(p,nest);
      times += [(cpuTime() - startTime) / 1000000];
      print(".");
    }
  }
  
  print("done\n");
  println("Times:");
  println(times);
}