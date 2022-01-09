module ide::vis::integrationtests::VisualizerTester

import ModelFinder;

import translation::AST;

import ide::Imploder;
import ide::vis::ModelVisualizer; 
import translation::SMTInterface;

import smtlogic::Core;

import IO; 

void translateAndVisMyFrstStr() = translateAndVis(|project://allealle/examples/str/myfirststr.alle|);

void translateAndVis(loc problem) = translateAndVis(implodeProblem(problem));

void translateAndVis(Problem p) {
  ModelFinderResult result = checkInitialSolution(p);
  
  switch(result) {
    case sat(Model currentModel, Model (Domain) nextModel, void () stop): renderModel(currentModel, nextModel, stop);
    case unsat(set[Formula] _) : println("Not satisfiable, can not visualize");
    case trivialSat(Model _) : println("Trivially satisfiable");
    case trivialUnsat() : println("Trivially not satisfiable");  
  }
}

