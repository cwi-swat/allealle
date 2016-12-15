module tests::ProblemRunner

import orig::ModelFinder;
import orig::Parser;
import orig::Imploder;
import orig::AST;
import orig::FormulaTranslator;

import IO;

void translateAndSolveSudoku() = translateAndSolve(|project://allealle/examples/sudoku.alle|);

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