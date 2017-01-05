module ide::tests::ImploderTest

import ide::Imploder;
import ide::CombinedAST;

import IO;

test bool implodeProblem() {
  try {
    Problem p = implodeProblem("{a,b,c,d}");
    return true;
  } catch ex: {
    println("Exception while imploding: <ex>");
    fail;
  }
}