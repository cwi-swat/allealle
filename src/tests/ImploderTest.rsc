module tests::ImploderTest

import relational::Imploder;
import relational::AST;

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