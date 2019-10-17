module util::tests::ModelPrinterTester

import util::ModelPrinter;

import ide::CombinedModelFinder;
import ide::CombinedImploder;
import ide::CombinedAST;

void testPrintModel() {
  ModelFinderResult mfr = checkInitialSolution(implodeProblem(|project://allealle/tests/specs/rebel_example.alle|));
  
  if (sat(Model currentModel, Model (Domain) nextModel, void () stop) := mfr) {
    printAlleModel(currentModel);
    stop();
  }
}