module ide::integrationtests::TranslationBenchmark

import theories::Binder;

import ide::Imploder;
import ide::CombinedAST;
import ide::CombinedModelFinder;
  
import IO;
import Set;

import util::Benchmark;

void translateBenchmark(loc p, int n) {
  Problem problem = implodeProblem(p);
  
  set[int] translationTimes = {};
  
  for (int i <- [0..n]) {
    println("\nStarting iteration: <i>");
    println("=======================\n");
    print("Building initial environment...");
    tuple[Environment env, int time] ie = bm(createInitialEnvironment, problem); 
    print("done, took: <(ie.time/1000000)> ms\n");
    
   
    println("Translating problem to SAT formula...");
    tuple[TranslationResult r, int time] t = bm(translateProblem, problem, ie.env);
    println("\n\nDone translating, took: <(t.time/1000000)> ms");
    
    translationTimes += t.time;
  }
  
  println("\n=====================");
  println("Average translation time was: <((0 | it + t | int t <- translationTimes) / n) / 1000000>");
  println("Maximal translation time was: <(0 | t > it ? t : it | int t <- translationTimes) / 1000000>");
  println("Minimal translation time was: <(getOneFrom(translationTimes) | t < it ? t : it | int t <- translationTimes) / 1000000>");  
}

private tuple[&T, int] bm(&T (&R) methodToBenchmark, &R p) {
  int startTime = userTime();
  &T result = methodToBenchmark(p);
  return <result, userTime() - startTime>;
}

private tuple[&T, int] bm(&T (&R,&Q) methodToBenchmark, &R p1, &Q p2) {
  int startTime = userTime();
  &T result = methodToBenchmark(p1,p2);
  return <result, userTime() - startTime>;
}