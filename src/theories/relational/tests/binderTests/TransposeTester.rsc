module theories::relational::tests::binderTests::TransposeTester

extend theories::relational::tests::binderTests::TesterBase;

test bool transposeOfUnaryRelationIsItself() {
  Universe uni = universe(["a","b"]);
  Binding unary = t("a") + t("b");

  return transpose(unary, uni) == unary;
}

test bool transposeOfBinary() {
  Universe uni = universe(["a","b","c"]);
  Binding binary = t("a","b") + t("a","c");
  
  return transpose(binary, uni) == t("b","a") + t("c","a");
}

test bool tranposeOfTenary() {
  Universe uni = universe(["a","b","c","d"]);
  Binding tenary = t("a","b","c") + t("a","b","d");
  
  return transpose(tenary, uni) == t("c","b","a") + t("d","b","a");
}