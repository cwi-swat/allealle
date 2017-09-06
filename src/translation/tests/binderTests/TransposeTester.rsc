module theories::tests::binderTests::TransposeTester

extend theories::tests::binderTests::TesterBase;

test bool transposeOfUnaryRelationIsItself() {
  RelationMatrix unary = t(["a"]) + t(["b"]);

  return transpose(unary) == unary;
}

test bool transposeOfBinary() {
  RelationMatrix binary = t(["a","b"]) + t(["a","c"]);
  
  return transpose(binary) == t(["b","a"]) + t(["c","a"]);
}

test bool tranposeOfTenary() {
  RelationMatrix tenary = t(["a","b","c"]) + t(["a","b","d"]);
  
  return transpose(tenary) == t(["c","b","a"]) + t(["d","b","a"]);
}