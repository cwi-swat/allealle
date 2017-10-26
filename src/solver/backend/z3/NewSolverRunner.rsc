module solver::backend::z3::NewSolverRunner

import solver::backend::z3::Z3;

import logic::Integer;
import translation::Translator;

void initSolver() {
  init(#Formula, #Command);
}

bool isSatisfiable(TranslationResult tr) {
  assertFormula(tr.relationalFormula);
  
  if (tr.attributeFormula != \true()) {
    assertFormula(tr.attributeFormula);
  }
  
  if (tr.additionalCommands != []) {
    for (Command c <- tr.additionalCommands) {
      addOptimizeCommand(c);
    }
  }
  
  check(); 
}