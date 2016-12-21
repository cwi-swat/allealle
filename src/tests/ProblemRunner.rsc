module tests::ProblemRunner

import ModelFinder;
import relational::Imploder;
import AST;
import Binder;
import Translator;

import IO;

void translateAndSolveSudoku() = translateAndSolve(|project://allealle/examples/relational/sudoku.alle|);

void translateAndSolve(loc alleAlleFile) {
  println("Done");
  Problem p = implodeProblem(alleAlleFile);
  
  for (int i <- [0..10]) {
    ModelFinderResult r = checkInitialSolution(p);
    if (sat(Environment currentModel, Universe universe, Environment () nextModel, void () stop) := r) {
     stop();
    }
  }  
}