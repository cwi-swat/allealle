module solver::backend::z3::Z3New

import logic::Integer;

@reflect @javaClass{solver.backend.z3.Z3}
public java void init(type[Formula] formType, type[Command] commandType);

@javaClass{solver.backend.z3.Z3}
public java void reset();

@reflect @javaClass{solver.backend.z3.Z3}
public java void assertFormula(Formula form);

@reflect @javaClass{solver.backend.z3.Z3}
public java void addOptimizeCommand(Command command);

@reflect @javaClass{solver.backend.z3.Z3}
public java void check();

test bool simpleFormula() {
  init(#Formula, #Command);
  assertFormula(\and({var("a"), var("b"), not(var("a"))}));
  check();
}