module tests::ProblemRunner

import relational::Imploder;
import relational::Translator;
import relational::SMTInterface;

import AST;
import Binder;
import Translator;
import ModelFinder;

import IO;

void translateAndSolveSudoku() = translateAndSolve(|project://allealle/examples/relational/sudoku.alle|);

void translateAndSolve(loc alleAlleFile) {
  Problem p = implodeProblem(alleAlleFile);
  
  for (int i <- [0..10]) {
    ModelFinderResult r = checkInitialSolution(p, [<getRelationalTranslator(), getRelationalSMTInterface()>]);
    if (sat(Environment currentModel, Universe universe, Environment () nextModel, void () stop) := r) {
     stop();
    }
  }  
}