module translation::tests::relationTests::ProjectionTester

import translation::Relation;
import translation::AST;

import translation::tests::relationTests::RelationBuilder;
import translation::tests::relationTests::DistinctTester;

import smtlogic::Core;
import smtlogic::Ints;

import IO;

test bool projectedFieldsMustBeInRelation() {
  Relation nest = create("nest", ("pId":id(),"hId":id())).t(("pId":key("p1"), "hId":key("h1"))).t(("pId":key("p1"), "hId":key("h2"))).build();
  
  try {
    projection(nest, {"non-existing"});
    fail;
  } catch ex: return true;
}

test bool projectionOfAllFieldsIsIsomorphic() {
  Relation nest = create("nest", ("pId":id(),"hId":id())).t(("pId":key("p1"), "hId":key("h1"))).t(("pId":key("p1"), "hId":key("h2"))).build();

  return nest == projection(nest, {"pId","hId"}); 
}

test bool projectionOfSingleFieldsCombinesDuplicateRows() {
  Relation nest = create("nest", ("pId":id(),"hId":id())).v(("pId":key("p1"), "hId":key("h1"))).v(("pId":key("p1"), "hId":key("h2"))).build();
  
  return projection(nest, {"pId"}) == create("pigeon", ("pId":id())).f(("pId":key("p1")), \or(pvar("nest_h1_p1"),pvar("nest_h2_p1")), \true()).build();
}

test bool projectionWithNonIdAttributeFieldsWithFixedValues() {
  Relation anchestor = create("anchestor", ("pre":id(),"des":id(), "between":\int()))
                          .v(("pre":key("p1"),"des":key("d1"),"between":term(lit(\int(20)))))
                          .v(("pre":key("p1"),"des":key("d2"),"between":term(lit(\int(40)))))
                          .build();
  
  return projection(anchestor, {"pre","between"}) == 
                       create("result", ("pre":id(),"between":\int()))
                          .f(("pre":key("p1"),"between":term(lit(\int(20)))), pvar("anchestor_d1_p1"), \true())
                          .f(("pre":key("p1"),"between":term(lit(\int(40)))), pvar("anchestor_d2_p1"), \true())
                          .build();
}

test bool projectionWithNonIdAttributeFieldsWithOpenValues() {
  Relation anchestor = create("anchestor", ("pre":id(),"des":id(), "between":\int()))
                          .v(("pre":key("p1"),"des":key("d1"),"between":term(var("b1",Sort::\int()))))
                          .v(("pre":key("p1"),"des":key("d2"),"between":term(var("b2",Sort::\int()))))
                          .build();
  
  Relation projectResult = projection(anchestor, {"pre","between"});
  
  bool part1 = projectResult == create("result", ("pre":id(),"between":\int()))
                                  .f(("pre":key("p1"),"between":term(var("b1",Sort::\int()))), pvar("anchestor_d1_p1"), \true())
                                  .f(("pre":key("p1"),"between":term(var("b2",Sort::\int()))), pvar("anchestor_d2_p1"), \true())
                                  .build();
                              
 
  bool part2 = checkAllDistinct(projectResult);
  
  return part1 && part2; 
}