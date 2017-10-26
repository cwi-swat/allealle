module translation::tests::binderTests::DisjunctionTester

extend translation::tests::binderTests::TesterBase;

test bool disjunctionWithOnlyTruthValuesOnlyResultsInTruthValues() {
  RelationMatrix lhs = truths([["a"],["c"]]);
  RelationMatrix rhs = truths([["a"],["b"],["d"]]);
  
  return or(lhs,rhs) == truths([["a"],["b"],["c"],["d"]]);
}

test bool disjunctionMatricesShouldBeOfSameArity() {
  RelationMatrix lhs = truths([["a"],["b"]]);
  RelationMatrix rhs = truths([["a","b"],["b","c"]]);
  
  try {
    or(lhs, rhs);
  } catch ex: {return true;}

  fail;
}

test bool disjunctionUsingVarsResultsInOrsInTheFormulas() {
  RelationMatrix lhs = var(["a"], "lhs");
  RelationMatrix rhs = var(["a"], "rhs");
  
  return or(lhs,rhs) == (["a"]:relOnly(\or({var("lhs_a"), var("rhs_a")})));
}

test bool disjunctionUsingVarsAndTruthValuesResultsInSingleFormulas() {
  RelationMatrix lhs = build([var(["a"], "lhs"),truth(["b"])]);
  RelationMatrix rhs = var(["b"], "rhs");

  return or(lhs,rhs) == build([(["a"]:relOnly(var("lhs_a"))), truth(["b"])]);
}