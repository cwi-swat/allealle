module relational::LatexResultBuilder

import lang::csv::IO;

import IO;
import List;
import util::Math;

alias RawResultRow = tuple[int config, int translationTime, int solvingTime, bool sat, int nrOfVars, int nrOfClauses];
alias RawResult = list[RawResultRow];

alias Config = tuple[str alleFile, str kodkodFile, list[str] superScript, list[int] includedRuns, str (int) nrOfAtoms, str (int) bitwidth]; 

map[str problem, Config cfg] included()
  = ("FileSystem" : <"filesystem/allealle_with_solve_5-10.csv", "filesystem/kodkod_with_solve_5-10.csv", ["r"], [5,10], str (int config) {return "<3 * config>"; }, str (int config) { return "-"; }>)
  + ("HandShake" : <"handshake/allealle_with_solve_10-17.csv", "handshake/kodkod_with_solve_10-17.csv", ["r","c"], [10,17], str (int config) {return "<config>"; }, str (int config) { return "<ceil(log2(config+1))>"; }>)
  + ("Account" : <"account/allealle_with_solve_5-10.csv", "account/kodkod_with_solve_5-9.csv", ["r","i"], [5,9], str (int config) { return "12"; }, str (int config) {return "<config>"; }>)
  + ("Rivercrossing" : <"rivercrossing/allealle_with_solve_1-1.csv", "rivercrossing/kodkod_with_solve_1-1.csv", ["r"], [1], str (int config) { return "12"; }, str (int config) { return "-"; }>) 
  + ("Square" : <"square/allealle_with_solve_4-10.csv", "square/kodkod_with_solve_4-10.csv", ["i"], [4,10], str (int config) {return "<2>";}, str (int config) { return "<config>"; }>)
  + ("Pigeonhole" : <"pigeonhole/allealle_with_solve_5-9.csv", "pigeonhole/kodkod_with_solve_5-9.csv", ["r"], [5,9], str (int config) { return "<(config * 2) - 1>"; }, str (int config) { return "-"; }>);
  
list[str] order = ["FileSystem","HandShake","Pigeonhole", "Rivercrossing", "Square", "Account"];

void buildResultTable() = buildResultTable(|home:///workspace/papers/onward2019/benchmark/relational/compare.tex|);

void buildResultTable(loc resultFile) {
  loc base = |project://allealle-benchmark/results/relational/|;
  config = included();
  
  str table = header();
     
  for (str problem <- order) {
    RawResult alle = readResultCsv(base + config[problem].alleFile);
    RawResult kodkod = readResultCsv(base + config[problem].kodkodFile);
    
    for (aResult <- alle, aResult.config in config[problem].includedRuns, kResult := findConfig(aResult.config, kodkod, problem)) {
      table += "<row(problem, aResult.config, aResult, kResult, config[problem])>";
    } 
  }
  
  table += footer();
  
  writeFile(resultFile, table);
}

private str row(str problem, int curConfig, RawResultRow alle, RawResultRow kodkod, Config cfg) 
  = "    <problem><showSuperScript(cfg.superScript)> & \\num{<cfg.nrOfAtoms(curConfig)>} & <cfg.bitwidth(curConfig)> & <alle.sat ? "SAT" : "UNSAT"> & \\num{<alle.translationTime>} & \\num{<alle.solvingTime>} & \\num{<alle.nrOfVars>} & \\num{<alle.nrOfClauses>} & \\num{<kodkod.translationTime>} & \\num{<kodkod.solvingTime>} & \\num{<kodkod.nrOfVars>} & \\num{<kodkod.nrOfClauses>} \\\\\n"; 

private str showSuperScript(list[str] ss) = "$^{<intercalate(",", ss)>}$";

private RawResultRow findConfig(int config, RawResult result, str problem) {
  for (r <- result, r.config == config) {
    return r;
  }
  
  throw "Unable to find config <config> in kodkod result for problem <problem>";
}

private str header() 
  = "  \\begin{tabular}{@{}lrrlrrrrrrrr@{}}\\toprule
    '    & & & & \\multicolumn{4}{c}{\\alle} & \\multicolumn{4}{c}{\\kodkod} \\\\
    '    \\cmidrule{5-8} \\cmidrule{9-12}
    '    \\thead{Problem} & \\thead{\\#Atoms} & \\thead{Bit width\\\\(\\kodkod only)} & \\thead{Sat?} & \\thead{Trans. time\\\\(in ms)} & \\thead{Solve time\\\\(in ms)} & \\thead{\\#Vars} & \\thead{\\#Clauses} & \\thead{Trans. time\\\\(in ms)} & \\thead{Solve time\\\\(in ms)} & \\thead{\\#Vars} & \\thead{\\#Clauses} \\\\
    '    \\midrule\n";

private str footer() 
  = "     \\bottomrule\\addlinespace[\\belowrulesep]
    '     \\multicolumn{12}{@{}l}{\\footnotesize Problem contains r) relational constraints, c) cardinality constraints, i) integer constraints}
    '  \\end{tabular}";

RawResult readResultCsv(loc file) = readCSV(#RawResult, file);
