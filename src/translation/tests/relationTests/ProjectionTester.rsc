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
  Relation nest = create("nest", ("pId":id(),"hId":id())).t(("pId":key("p1"), "hId":key("h1"))).t(("pId":key("p1"), "hId":key("h2"))).build();
  
  try {
    project(nest, {"non-existing"});
    fail;
  } catch ex: return true;
}

test bool projectOfAllFieldsIsIsomorphic() {
  Relation nest = create("nest", ("pId":id(),"hId":id())).t(("pId":key("p1"), "hId":key("h1"))).t(("pId":key("p1"), "hId":key("h2"))).build();

  return nest == project(nest, {"pId","hId"}); 
}

test bool projectOfSingleFieldsCombinesDuplicateRows() {
  Relation nest = create("nest", ("pId":id(),"hId":id())).v(("pId":key("p1"), "hId":key("h1"))).v(("pId":key("p1"), "hId":key("h2"))).build();
  
  Relation projectResult = project(nest, {"pId"});
  
  bool part1 = projectResult == create("pigeon", ("pId":id())).f(("pId":key("p1")), \or(pvar("nest_h1_p1"),pvar("nest_h2_p1")), \true()).build();
  bool part2 = checkAllDistinct(projectResult);
  
  return part1 && part2;
}

test bool projectWithNonIdAttributeFieldsWithFixedValues() {
  Relation anchestor = create("anchestor", ("pre":id(),"des":id(), "between":\int()))
                          .v(("pre":key("p1"),"des":key("d1"),"between":term(lit(\int(20)))))
                          .v(("pre":key("p1"),"des":key("d2"),"between":term(lit(\int(40)))))
                          .build();

  Relation projectResult = project(anchestor, {"pre","between"});
   
  bool part1 = projectResult == create("result", ("pre":id(),"between":\int()))
                          .f(("pre":key("p1"),"between":term(lit(\int(20)))), pvar("anchestor_d1_p1"), \true())
                          .f(("pre":key("p1"),"between":term(lit(\int(40)))), pvar("anchestor_d2_p1"), \true())
                          .build();
  bool part2 = checkAllDistinct(projectResult);

  
  return part1 && part2;
}

test bool projectWithNonIdAttributeFieldsWithOpenValues() {
  Relation anchestor = create("anchestor", ("pre":id(),"des":id(), "between":\int()))
                          .v(("pre":key("p1"),"des":key("d1"),"between":term(var("b1",Sort::\int()))))
                          .v(("pre":key("p1"),"des":key("d2"),"between":term(var("b2",Sort::\int()))))
                          .v(("pre":key("p1"),"des":key("d3"),"between":term(var("b3",Sort::\int()))))
                          .v(("pre":key("p1"),"des":key("d4"),"between":term(var("b4",Sort::\int()))))
                          .v(("pre":key("p1"),"des":key("d5"),"between":term(var("b5",Sort::\int()))))
                          .build();
  
  Relation projectResult = project(anchestor, {"pre","between"});
  
  bool part1 = size(projectResult.rows) == 5;
  bool part2 = checkAllDistinct(projectResult);
  
  return part1 && part2; 
}