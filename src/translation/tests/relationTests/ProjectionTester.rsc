module translation::tests::relationTests::ProjectionTester

import translation::Relation;
import translation::AST;

import translation::tests::relationTests::RelationBuilder;
import translation::tests::relationTests::DistinctTester;

import smtlogic::Core;
import smtlogic::Ints;

import IO;
import Map;

test bool projectedFieldsMustBeInRelation() {
  Relation nest = create("nest", ("pId":id(),"hId":id())).t(("pId":lit(id("p1")), "hId":lit(id("h1")))).t(("pId":lit(id("p1")), "hId":lit(id("h2")))).build();
  
  try {
    project(nest, {"non-existing"});
    fail;
  } catch ex: return true;
}

test bool projectOfAllFieldsIsIsomorphic() {
  Relation nest = create("nest", ("pId":id(),"hId":id())).t(("pId":lit(id("p1")), "hId":lit(id("h1")))).t(("pId":lit(id("p1")), "hId":lit(id("h2")))).build();

  return nest == project(nest, {"pId","hId"}); 
}

test bool projectOfSingleFieldsCombinesDuplicateRows() {
  Relation nest = create("nest", ("pId":id(),"hId":id())).v(("pId":lit(id("p1")), "hId":lit(id("h1")))).v(("pId":lit(id("p1")), "hId":lit(id("h2")))).build();
  
  Relation projectResult = project(nest, {"pId"});
  
  bool part1 = projectResult == create("pigeon", ("pId":id())).f(("pId":lit(id("p1"))), \or(pvar("nest_h1_p1"),pvar("nest_h2_p1")), \true()).build();
  bool part2 = checkAllDistinct(projectResult);
  
  return part1 && part2;
}

test bool projectWithNonIdAttributeFieldsWithFixedValues() {
  Relation anchestor = create("anchestor", ("pre":id(),"des":id(), "between":Domain::\int()))
                          .v(("pre":lit(id("p1")),"des":lit(id("d1")),"between":lit(\int(20))))
                          .v(("pre":lit(id("p1")),"des":lit(id("d2")),"between":lit(\int(40))))
                          .build();

  Relation projectResult = project(anchestor, {"pre","between"});
   
  bool part1 = projectResult == create("result", ("pre":id(),"between":Domain::\int()))
                          .f(("pre":lit(id("p1")),"between":lit(\int(20))), pvar("anchestor_d1_p1"), \true())
                          .f(("pre":lit(id("p1")),"between":lit(\int(40))), pvar("anchestor_d2_p1"), \true())
                          .build();
  bool part2 = checkAllDistinct(projectResult);

  
  return part1 && part2;
}

test bool projectWithNonIdAttributeFieldsWithOpenValues() {
  Relation anchestor = create("anchestor", ("pre":id(),"des":id(), "between":Domain::\int()))
                          .v(("pre":lit(id("p1")),"des":lit(id("d1")),"between":var("b1",Sort::\int())))
                          .v(("pre":lit(id("p1")),"des":lit(id("d2")),"between":var("b2",Sort::\int())))
                          .v(("pre":lit(id("p1")),"des":lit(id("d3")),"between":var("b3",Sort::\int())))
                          .v(("pre":lit(id("p1")),"des":lit(id("d4")),"between":var("b4",Sort::\int())))
                          .v(("pre":lit(id("p1")),"des":lit(id("d5")),"between":var("b5",Sort::\int())))
                          .build();
  
  Relation projectResult = project(anchestor, {"pre","between"});
  
  bool part1 = size(projectResult.rows) == 5;
  bool part2 = checkAllDistinct(projectResult);
  
  return part1 && part2; 
}