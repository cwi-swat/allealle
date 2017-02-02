module ide::tests::ProbemRunner

import AST;
import Binder;
import Translator;
import ModelFinder;

import ide::Imploder;
import ide::CombinedTranslationUnits;
 
import IO;

void translateAndSolveSudoku() = translateAndSolve(|project://allealle/examples/relational/sudoku.alle|,1);
void translateAndSolveTriangle() = translateAndSolve(|project://allealle/examples/int/triangle.alle|,1);
void translateAndSolveRiverCrossing() = translateAndSolve(|project://allealle/examples/relational/rivercrossing.alle|,1);

void translateAndSolve(loc alleAlleFile, int nrOfTestsToPerform) {
  Problem p = implodeProblem(alleAlleFile);
  
  for (int i <- [0..nrOfTestsToPerform]) {
    ModelFinderResult r = checkInitialSolution(p, getTranslationUnits());
    if (sat(Environment currentModel, Universe universe, Environment () nextModel, void () stop) := r) {
     stop();
    }
  }  
}

void performTest(int nr) = translateAndSolve(|project://allealle/examples/relational/rivercrossing.alle|,nr);