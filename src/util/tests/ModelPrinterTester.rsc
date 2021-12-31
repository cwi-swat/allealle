module util::tests::ModelPrinterTester

import IO;

import util::ModelPrinter;

import ModelFinder;
import ide::Imploder;
import translation::AST;
import translation::SMTInterface;

void solveAndPrintModel(loc problem) {
  ModelFinderResult mfr = checkInitialSolution(implodeProblem(problem));
  
  switch(mfr) {
	case sat(Model currentModel, Model (Domain) nextModel, void () stop): { 
		printAlleModel(currentModel);
    	stop();
  	}
  	case unsat(_): 					println("Unsat");
	case trivialSat(Model model):   printAlleModel(model);
	case trivialUnsat(): 			println("Trivially Unsat");
	case timeout(): 				println("Solver timed out");
	case unknown():					println("Unknown");
  }
}