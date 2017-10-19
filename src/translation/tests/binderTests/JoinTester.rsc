module translation::tests::binderTests::JoinTester

extend translation::tests::binderTests::TesterBase;

test bool join_1x2_results_1_when_overlap_occurs() {
  nest = vars([["p1","h1"],["p1","h2"],["p2","h1"],["p2","h2"]], "nest");
  p = truth(["p1"]);

  list[str] uni = constructUniverse([p,nest]);
  
  return convert(dotJoin(convert(p, uni), convert(nest, uni)), uni) == compose([var(["h1"], var("nest_p1_h1")), var(["h2"], var("nest_p1_h2"))]);
}

test bool empty_result_when_no_matching_columns() {
  nest = vars([["p1","h1"],["p1","h2"],["p2","h1"],["p2","h2"]], "nest");
  p = truth(["p1"]);

  list[str] uni = constructUniverse([p,nest]);
  
  return convert(dotJoin(convert(nest, uni), convert(p, uni)), uni) == ();
}

test bool join_3x1_and_1x3_results_2_when_matching_columns() {
  a = truths([["a","a","a"],["a","b","c"],["b","a","b"]]);
  b = truths([["b"],["c"]]);

  list[str] uni = constructUniverse([a,b]);
  
  return convert(dotJoin(convert(a,uni),convert(b,uni)), uni) == truths([["a","b"],["b","a"]]) &&
         convert(dotJoin(convert(b,uni),convert(a,uni)), uni) == truths([["a","b"]]);
}  