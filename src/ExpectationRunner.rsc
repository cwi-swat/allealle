module ExpectationRunner

import ModelFinder;
import translation::AST;
import translation::SMTInterface;

import util::Maybe;
import IO;

data ExpectationResult
  = success()
  | failed(str reason)
  ;

ExpectationResult checkExpectation(Problem p) {
  if (just(Expect e) := p.expect) {
    ModelFinderResult mfr = checkInitialSolution(p);
    return interpret(mfr,e);    
  } else {
    throw "No expectation in problem";
  }
}

ExpectationResult interpret(sat(_, Model (Domain) nextModel, void () stop), Expect e) {
  if (e.result == sat()) {
    // todo interpret possible nr of model restriction
    r = (e has restrict) ? interpret(e.restrict.expr, e.restrict.d, nextModel) : success();
    stop();

    return r;  
  } else {
    return failed("Expected <toStr(e.result)> but was sat");
  }
}

ExpectationResult interpret(unsat(_), Expect e) {
  if (e.result == unsat()) {
    return success();  
  } else {
    return failed("Expected <toStr(e.result)> but was unsat");
  }
}

ExpectationResult interpret(trivialSat(_), Expect e) {
  if (e.result == trivSat()) {
    return success();  
  } else {
    return failed("Expected <toStr(e.result)> but was trivial sat");
  }
}

ExpectationResult interpret(trivialUnsat(_), Expect e) {
  if (e.result == trivUnsat()) {
    return success(); 
  } else {
    return failed("Expected <toStr(e.result)> but was trivial unsat");
  }
}

ExpectationResult interpret(eqMod(int nr), Domain d, Model (Domain) nextModel) {
  if (nr < 1) {
    throw "Expected models must be \>= 1";
  }
  
  int i = 1;
  while (empty() !:= nextModel(d)) {
    i += 1;
    if (i > nr) {
      return failed("Expected <nr> model(s) but there are \><nr> possible models");
    }
  }
  
  if (i < nr) {
    return failed("Expected <nr> model(s) but there are <i> possible models");
  } else {
    return success();
  }
}  

ExpectationResult interpret(ltMod(int nr), Domain d, Model (Domain) nextModel) {
  if (nr < 2) {
    throw "Expected models must be \>= 2";
  }
  
  int i = 1;
  while (empty() !:= nextModel(d)) {
    i += 1;
    if (i >= nr) {
      return failed("Expected less than <nr> model(s) but there are more possible models");
    }
  }
  
  return success();
}  

ExpectationResult interpret(gtMod(int nr), Domain d, Model (Domain) nextModel) {
  if (nr < 1) {
    throw "Expected models must be \>= 1";
  }
  
  int i = 1;
  while (empty() !:= nextModel(d)) {
    i += 1;
    if (i > nr) {
      return success();
    }
  }
  
  return failed("Expected more than <nr> model(s) but there are <i> possible models");
}  

str toStr(sat()) = "sat";
str toStr(trivSat()) = "trivial sat";
str toStr(unsat()) = "unsat";
str toStr(trivUnsat()) = "trivial unsat";