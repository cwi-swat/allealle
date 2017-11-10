module benchmark::kodkod::pigeonhole::AlleAlleBenchmark

import List;
import Set;
import util::Benchmark;
import IO;
import Map;

import ide::CombinedModelFinder;
import ide::CombinedAST;
import ide::Imploder;   

import translation::Environment;
import translation::Translator;
import translation::Binder;
import logic::Propositional;

import util::MemoCacheClearer;

alias Statistic = tuple[int nrOfAtoms, int config, int translationTime, int vars, int clauses];

void runBenchmark() = runBenchmark(10, 100, 10, |project://allealle-benchmark/benchmark/results/kodkod-comparison/allealle-results_listIndices_withMemo_compiled.csv|, true);

set[str] alleAlleMods() = {"translation::Environment","translation::Binder"};

str generatePigeonProblem(int nrOfPigeons, int nrOfHoles) = 
  "Pigeon (1) = {<intercalate(",",["\<p<i>\>" | i <- [1..nrOfPigeons+1]])>}
  'Hole (1) = {<intercalate(",",["\<h<i>\>" | i <- [1..nrOfHoles+1]])>}
  'nest (2) \<= {<intercalate(",",["\<p<i>,h<j>\>" | i <- [1..nrOfPigeons+1], j <- [1..nrOfHoles+1]])>}
  '
  'nest in Pigeon-\>Hole
  'forall p:Pigeon | one p.nest
  'forall h:Hole | lone nest.h";
  
void runBenchmark(int startNrOfAtoms, int endNrOfAtoms, int runsPerConfig, loc csv, bool saveResult) {
  println("Warming up");
  Problem warmup = implodeProblem(generatePigeonProblem(startNrOfAtoms,startNrOfAtoms-1));
  for (int i <- [0..20]) {
    translate(startNrOfAtoms, i, warmup);
  } 
  println("Warm up done");
  
  clearMemoCache(alleAlleMods(), debug = true);

  map[int, list[Statistic]] benchmarkResult = ();
  
  for (int i <- [0..endNrOfAtoms-startNrOfAtoms]) {
    print("Start translating for <i+startNrOfAtoms> pigeons and <i+startNrOfAtoms-1> holes: ");
    benchmarkResult[i] = [];
        
    Problem p = implodeProblem(generatePigeonProblem(i+startNrOfAtoms,i+startNrOfAtoms-1));
    for (int r <- [0..runsPerConfig]) {
      benchmarkResult[i] += translate(i+startNrOfAtoms, r, p);
      print(".");
    }
    print("done\n");
  } 
    
  if (saveResult) {
    println("Completely done, saving to csv");
    saveToCSV(benchmarkResult, startNrOfAtoms, csv);
  }
  else {
    println("Completely done, NOT saving to csv");
  }
}

private void saveToCSV(map[int, list[Statistic]] benchmarkTimes, int startNrOfAtoms, loc csvLoc) {
  println(benchmarkTimes);
  map[int, Statistic] aggregated = aggregate(benchmarkTimes);
  str csv = "#Config,TranslationTime,#Vars,#Clauses <for (int i <- sort(domain(aggregated))) {>
            '<aggregated[i].nrOfAtoms>,<aggregated[i].translationTime>,<aggregated[i].vars>,<aggregated[i].clauses><}>";
            
  writeFile(csvLoc, csv);
}

private int countPrimVars(Environment env) = size(collectSMTVars(env));

@memo
private int countClauses(TranslationResult r) {
  int nrOfClauses = 0;
  visit(r.relationalFormula) {
    case Formula _ : nrOfClauses += 1;
  }
  
  return nrOfClauses;
}

private Statistic translate(int nrOfAtoms, int config, Problem p) {
  clearMemoCache(alleAlleMods());
  
  int startTime = cpuTime();
  Environment env = createInitialEnvironment(p);
  TranslationResult r = translateProblem(p, env, logIndividualFormula = false);
  int endTime = cpuTime(); 
  
  int primVars = countPrimVars(env);
  int clauses = countClauses(r);
  
  return <nrOfAtoms, config, (endTime - startTime) / 1000000, primVars, clauses>; 
}

private list[Statistic] sortByTranslationTime(list[Statistic] stats) 
  = sort(stats, bool (Statistic a, Statistic b) { return a.translationTime < b.translationTime;});

private map[int, Statistic] aggregate(map[int, list[Statistic]] benchmarkTimes) {
  map[int, Statistic] aggregated = ();
     
  for (int i <- benchmarkTimes) {
    list[Statistic] sorted = sortByTranslationTime(benchmarkTimes[i]);
    // get the mean
    int mean;
    if (size(sorted)%2 == 0) {
      mean = (sorted[size(sorted)/2].translationTime + sorted[size(sorted)/2 + 1].translationTime) / 2;
    } else {
      mean = sorted[size(sorted)/2].translationTime;
    } 
    Statistic s = getOneFrom(benchmarkTimes[i]);

    aggregated[i] = <s.nrOfAtoms, 0, mean, s.vars, s.clauses>;           
  }
  
  return aggregated;
}
