module translation::tests::binderTests::Benchmark

extend translation::tests::binderTests::TesterBase;

import util::Benchmark;
import util::MemoCacheClearer;

RelationMatrix constructPigeonRelation(int nrOfPigeons) = truths([["p<i>"] | int i <- [1..nrOfPigeons+1]]);
RelationMatrix constructHoleRelation(int nrOfHoles) = truths([["h<i>"] | int i <- [1..nrOfHoles+1]]);
RelationMatrix constructNestRelation(RelationMatrix pigeons, RelationMatrix holes) = vars([[p,h] | [str p] <- pigeons, [str h] <- holes], "nest");

void clearCache() = clearMemoCache({"translation::Binder","translation::Translator"});

void runJoinBenchmark(int nrOfPigeons, int nrOfHoles, int warmup, int nrOfRounds) {
  println("Preparing \'dot join\' benchmark for <nrOfPigeons> pigeons and <nrOfHoles> holes");

  pigeons = constructPigeonRelation(nrOfPigeons);
  holes = constructHoleRelation(nrOfHoles);
  nest = constructNestRelation(pigeons, holes);
 
  print("Warming up (<warmup> rounds): ");
  for (int i <- [0..warmup]) {
    r = dotJoin(pigeons,nest);
    print(".");
    clearCache();
  }
  print("done\n");
  
  list[int] times = [];
  
  print("Running benchmark (<nrOfRounds> total iterations): ");
  for (int i <- [0..nrOfRounds]) {
    int startTimeWholeLoop = cpuTime();
    for (Index idx <- holes) {
      clearCache();
      RelationMatrix h = (idx : holes[idx]);
      int startTime = cpuTime();
      r = dotJoin(nest,h);
      times += [(cpuTime() - startTime) / 1000000];
      print(".");
    }
    times += [(cpuTime() - startTimeWholeLoop) / 1000000];
  }
  
  print("done\n");
  println("Times:");
  println(times);
}

list[str] alphabet() = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z"];

void runProductBenchmark(int warmup, int rounds) {
  
  RelationMatrix m = ([a] : relOnly(\true()) | a <- alphabet());
    
  print("Warming up: ");
  for (int i <- [0..warmup]) {
    product(m,m);
    clearCache();
    print(".");
  }
  println("done\n");
  
  print("Running benchmark: ");
  list[int] times = [];
  
  for (int i <- [0..rounds]) {
    int startTime = cpuTime();
    r = product(m,m);
    times += [(cpuTime() - startTime) / 1000000];
    print(".");
    clearCache();
  } 
  print("done\n");
  
  println(times);
}

void runTransitiveClosureBenchmark(int warmup, int rounds) {
  
  RelationMatrix m = truths([["h","j"],["j","l"],["j","b"],["h","g"],["g","e"],["g","ji"]]);
    
  print("Warming up: ");
  for (int i <- [0..warmup]) {
    transitiveClosure(m);
    print(".");
    clearCache();
  }
  println("done\n");
  
  print("Running benchmark: ");
  list[int] times = [];
  
  for (int i <- [0..rounds]) {
    int startTime = cpuTime();
    r = transitiveClosure(m);
    times += [(cpuTime() - startTime) / 1000000];
    print(".");
    clearCache();
  } 
  print("done\n");
  
  println(times);
}