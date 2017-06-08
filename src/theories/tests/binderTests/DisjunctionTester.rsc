module theories::tests::binderTests::DisjunctionTester

extend theories::tests::binderTests::TesterBase;

test bool disjunctionWithOnlyTruthValuesOnlyResultsInTruthValues() {
  RelationMatrix lhs = t(["a"]) + f(["b"]) + t(["c"]) + f(["d"]);
  RelationMatrix rhs = t(["a"]) + f(["b"]) + f(["c"]) + t(["d"]);
  
  return disjunction(lhs,rhs) == t(["a"]) + f(["b"]) + t(["c"]) + t(["d"]);
}

test bool disjunctionMatricesShouldBeOfSameArity() {
  RelationMatrix lhs = t(["a"]) + f(["b"]);
  RelationMatrix rhs = t(["a","b"]) + f(["b","c"]);
  
  try {
    disjunction(lhs, rhs);
  } catch ex: {return true;}

  fail;
}

test bool disjunctionMissingVectorsOnEitherSideAreSeenAsFalseValues() {
  RelationMatrix lhs = t(["a"]) + f(["c"]);
  RelationMatrix rhs = t(["b"]);
  
  return disjunction(lhs,rhs) == t(["a"]) + t(["b"]) + f(["c"]);
}

test bool disjunctionUsingVarsResultsInOrsInTheFormulas() {
  RelationMatrix lhs = v(["a"], "lhs");
  RelationMatrix rhs = v(["a"], "rhs");
  
  return disjunction(lhs,rhs) == val(["a"], \or({var("lhs_a"), var("rhs_a")}));
}

test bool disjunctionUsingVarsAndTruthValuesResultsInSingleFormulas() {
  RelationMatrix lhs = v(["a"], "lhs") + t(["b"]);
  RelationMatrix rhs = f(["a"]) + v(["b"], "rhs");

  return disjunction(lhs,rhs) == v(["a"], "lhs") + t(["b"]);
}