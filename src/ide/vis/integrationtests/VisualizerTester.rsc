module ide::vis::integrationtests::VisualizerTester

import translation::Binder; 

import ide::CombinedAST;
import ide::CombinedModelFinder;
import ide::CombinedImploder;
import ide::vis::ModelVisualizer; 

import IO; 

void translateAndVis(loc problem) { 
  Problem p = implodeProblem(problem);
  
  ModelFinderResult result = checkInitialSolution(p);
  
  switch(result) {
    case sat(Model currentModel, Model (Domain) nextModel, void () stop): renderModel(currentModel, nextModel, stop);
    case unsat(set[Formula] unsatCore) : println("Not satisfiable, can not visualize");
    case trivialSat(Model model) : println("Trivially satisfiable");
    case trivialUnsat() : println("Trivially not satisfiable");  
  }
}

