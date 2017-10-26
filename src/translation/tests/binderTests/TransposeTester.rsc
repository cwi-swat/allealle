module translation::tests::binderTests::TransposeTester

extend translation::tests::binderTests::TesterBase;


test bool transposeOfBinary() {
  RelationMatrix binary = truths([["a","b"],["a","c"]]);
  
  return transpose(binary) == truths([["b","a"],["c","a"]]);
}

test bool transposeOfIdentityIsItself() {
  RelationMatrix iden = truths([["a","a"],["b","b"],["c","c"]]);
  
  return transpose(iden) == iden;
}

test bool canOnlyTransposeBinaryRelations() {
  RelationMatrix unary = truths([["a"],["b"],["c"]]);
  try {
    transpose(unary);
    fail;
  } catch ex: {};
  
  RelationMatrix tenary = truths([["a","b","c"],["c","d","e"]]);
  try {
    transpose(tenary);
    fail;
  } catch ex: {};
  
  return true;
}
