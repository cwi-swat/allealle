module translation::tests::binderTests::Benchmark

extend translation::tests::binderTests::TesterBase;

import util::Benchmark;

list[str] alphabet() = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z"];

void runProductBenchmark(int warmup, int rounds) {
  
  RelationMatrix m = ([a] : relOnly(\true()) | a <- alphabet());
    
  print("Warming up: ");
  for (int i <- [0..warmup]) {
    product(m,m);
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
  }
  println("done\n");
  
  print("Running benchmark: ");
  list[int] times = [];
  
  for (int i <- [0..rounds]) {
    int startTime = cpuTime();
    r = transitiveClosure(m);
    times += [(cpuTime() - startTime) / 1000000];
    print(".");
  } 
  print("done\n");
  
  println(times);
}