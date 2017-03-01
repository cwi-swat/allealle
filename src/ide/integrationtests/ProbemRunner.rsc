module ide::integrationtests::ProbemRunner

import theories::AST;
import theories::Binder;
import theories::Translator;
import ModelFinder;

import ide::Imploder;
import ide::CombinedModelFinder;
  
import IO;

void translateAndSolveSudoku() = translateAndSolve(|project://allealle/examples/relational/sudoku.alle|,1);
void translateAndSolveTriangle() = translateAndSolve(|project://allealle/examples/int/triangle.alle|,1);
void translateAndSolveRiverCrossing() = translateAndSolve(|project://allealle/examples/relational/rivercrossing.alle|,1);

void translateAndSolve(loc alleAlleFile, int nrOfTestsToPerform) = translateAndSolve(implodeProblem(alleAlleFile), nrOfTestsToPerform);
void translateAndSolve(str problem, int nrOfTestsToPerform) = translateAndSolve(implodeProblem(problem), nrOfTestsToPerform);

void translateAndSolve(Problem p, int nrOfTestsToPerform) {
  for (int i <- [0..nrOfTestsToPerform]) {
    ModelFinderResult r = checkInitialSolution(p);
    if (sat(Environment currentModel, Universe universe, Environment () nextModel, void () stop) := r) {
     stop();
    }
  }   
}

void performanceTestRiverCrossing(int nr) = translateAndSolve(|project://allealle/examples/relational/rivercrossing.alle|,nr);
void performanceTestSudoku(int nr) = translateAndSolve(|project://allealle/examples/relational/sudoku.alle|,nr);