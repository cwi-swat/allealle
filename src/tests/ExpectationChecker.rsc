module tests::ExpectationChecker

import ide::CombinedImploder;
import ide::CombinedAST;
import ide::CombinedExpectationRunner;

import IO;
import util::Maybe;

void checkAll() = checkAll(|project://allealle/tests|);

void checkAll(loc root) {
  if (!isDirectory(root)) {
    throw "Given root should be a directory";
  }

  map[loc, ExpectationResult] result = checkDir(root);
  
  bool failedChecks = false;
  
  println("");
  println("==========================");
  println("Done checking expectation.");
  
  for (file <- result, failed(str reason) := result[file]) {
    failedChecks = true;
    println("FAIL: (<file>) <reason>");
  }
  if (!failedChecks) {
    println("No errors found. All good.");
  } 
  
  println("==========================");
  println();
}

map[loc,ExpectationResult] checkDir(loc root) {
  if (!isDirectory(root)) {
    throw "Given root should be a directory";
  }

  map[loc, ExpectationResult] result = ();
  
  for (loc file <- root.ls) {
    if (isDirectory(file)) {
      result += checkDir(file);
    } else {
      if (just(ExpectationResult e) := checkFile(file)) {
        result[file] = e;
      }
    }
  }
  
  return result; 
}

Maybe[ExpectationResult] checkFile(loc file) {
  Problem p = implodeProblem(file);
  if (just(Expect e) := p.expect) {
    return just(checkExpectation(p));
  } else {
    return nothing();
  }
}
