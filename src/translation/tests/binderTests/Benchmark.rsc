module translation::tests::binderTests::Benchmark

extend translation::tests::binderTests::TesterBase;

import util::Benchmark;

SimpleRelationMatrix constructPigeonRelation(int nrOfPigeons) = truths([["p<i>"] | int i <- [1..nrOfPigeons+1]]);
SimpleRelationMatrix constructHoleRelation(int nrOfHoles) = truths([["h<i>"] | int i <- [1..nrOfHoles+1]]);
SimpleRelationMatrix constructNestRelation(SimpleRelationMatrix pigeons, SimpleRelationMatrix holes) = vars([[p,h] | [str p] <- pigeons, [str h] <- holes], "nest");

void runJoinBenchmark(int nrOfPigeons, int nrOfHoles, int warmup, int nrOfRounds) {
  println("Preparing \'dot join\' benchmark for <nrOfPigeons> pigeons and <nrOfHoles> holes");

  pigeons = constructPigeonRelation(nrOfPigeons);
  holes = constructHoleRelation(nrOfHoles);
  nest = constructNestRelation(pigeons, holes);
  
  list[str] uni = constructUniverse([pigeons,holes,nest]);
  
  RelationMatrix cPigeons = convert(pigeons, uni);
  RelationMatrix cHoles = convert(holes, uni);
  RelationMatrix cNest = convert(nest, uni);
  
  print("Warming up (<warmup> rounds): ");
  for (int i <- [0..warmup]) {
    dotJoin(cPigeons,cNest);
    print(".");
  }
  print("done\n");
  
  list[int] times = [];
  
  print("Running benchmark (<nrOfRounds> total iterations): ");
  for (int i <- [0..nrOfRounds]) {
    int startTime = cpuTime();
    dotJoin(cPigeons,cNest);
    times += [(cpuTime() - startTime) / 1000000];
    print(".");
  }
  
  print("done\n");
  println("Times:");
  println(times);
}