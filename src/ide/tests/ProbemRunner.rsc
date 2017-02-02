module ide::tests::ProbemRunner

import AST;
import Binder;
import Translator;
import ModelFinder;

import ide::Imploder;
import ide::CombinedTranslationUnits;
 
import IO;

void translateAndSolveSudoku() = translateAndSolve(|project://allealle/examples/relational/sudoku.alle|);
void translateAndSolveTriangle() = translateAndSolve(|project://allealle/examples/int/triangle.alle|);
void translateAndSolveRiverCrossing() = translateAndSolve(|project://allealle/examples/relational/rivercrossing.alle|);

void translateAndSolve(loc alleAlleFile) {
  Problem p = implodeProblem(alleAlleFile);
  
  for (int i <- [0..1]) {
    ModelFinderResult r = checkInitialSolution(p, getTranslationUnits());
    if (sat(Environment currentModel, Universe universe, Environment () nextModel, void () stop) := r) {
     stop();
    }
  }  
}