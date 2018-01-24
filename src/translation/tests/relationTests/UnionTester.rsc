module translation::tests::relationTests::UnionTester

import translation::Relation;
import translation::AST;

import translation::tests::relationTests::RelationBuilder;
import translation::tests::relationTests::DistinctTester;

import smtlogic::Core;
import smtlogic::Ints;

import IO;

test bool unionCompatibleRelationsCanBeUnified() {
  Relation r1 = create("rel1", ("id":id())).t(("id":key("r1"))).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":key("r2"))).build();
  
  return union(r1,r2) == create("result", ("id":id())).t(("id":key("r1"))).t(("id":key("r2"))).build();
}   

test bool unionIncompatibleRelationsCannotBeUnified() {
  Relation r1 = create("rel1", ("id1":id())).t(("id1":key("r1"))).build();
  Relation r2 = create("rel2", ("id2":id())).t(("id2":key("r2"))).build();

  try {
    union(r1,r2);
    fail;
  } catch e: ;     
  
  return true;
}

test bool unionIsCommutative() {
  Relation r1 = create("rel1", ("id":id())).t(("id":key("r1"))).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":key("r2"))).build();

  return union(r1,r2) == union(r2,r1);  
}

test bool unionIsAssociative() {
  Relation r1 = create("rel1", ("id":id())).t(("id":key("r1"))).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":key("r2"))).build();
  Relation r3 = create("rel3", ("id":id())).t(("id":key("r3"))).build();

  return union(union(r1,r2),r3) == union(r1,union(r2,r3));  
}

test bool mandatoryRowsTrumpOptionalRowsAfterUnion() {
  Relation r1 = create("rel1", ("id":id())).t(("id":key("r1"))).t(("id":key("r2"))).build();
  Relation r2 = create("rel2", ("id":id())).v(("id":key("r2"))).build();
  
  return union(r1,r2) == create("result", ("id":id())).t(("id":key("r1"))).t(("id":key("r2"))).build();
}

test bool twoOptionalRowsStayOptionalAfterUnion() {
  Relation r1 = create("rel1", ("id":id())).t(("id":key("r1"))).v(("id":key("r2"))).build();
  Relation r2 = create("rel2", ("id":id())).v(("id":key("r2"))).build();
  
  return union(r1,r2) == create("result", ("id":id())).t(("id":key("r1"))).f(("id":key("r2")), \or(pvar("rel1_r2"),pvar("rel2_r2")), \true()).build();
}

test bool unionOfNAryRelationsIsAllowed() {
  Relation r1 = create("rel1", ("pId":id(),"hId":id())).t(("pId":key("p1"),"hId":key("h1"))).t(("pId":key("p1"),"hId":key("h2"))).build();
  Relation r2 = create("rel2", ("pId":id(),"hId":id())).v(("pId":key("p1"),"hId":key("h2"))).build();

  return union(r1,r2) == create("result", ("pId":id(),"hId":id()))
    .t(("pId":key("p1"),"hId":key("h1")))
    .t(("pId":key("p1"),"hId":key("h2")))
    .build();
}
 
test bool unionWithExtraAttributes_WithSameFixedValuesResultsInSingleTuple() {
  Relation r1 = create("rel1", ("pId":id(),"age":Domain::\int())).t(("pId":key("p1"),"age":term(lit(\int(20))))).build();
  Relation r2 = create("rel2", ("pId":id(),"age":Domain::\int())).v(("pId":key("p1"),"age":term(lit(\int(20))))).build();

  return union(r1,r2) == create("result", ("pId":id(), "age":Domain::\int())).t(("pId":key("p1"), "age":term(lit(\int(20))))).build();
}

test bool unionWithExtraAttributes_WithDifferentFixedValuesResultsInTwoTuples() {
  Relation r1 = create("rel1", ("pId":id(),"age":Domain::\int())).t(("pId":key("p1"),"age":term(lit(\int(20))))).build();
  Relation r2 = create("rel2", ("pId":id(),"age":Domain::\int())).v(("pId":key("p1"),"age":term(lit(\int(30))))).build();

  return union(r1,r2) == create("result", ("pId":id(), "age":Domain::\int())).t(("pId":key("p1"), "age":term(lit(\int(20))))).f(("pId":key("p1"), "age":term(lit(\int(30)))), \pvar("rel2_p1"), \true()).build();
}

test bool unionWithExtraAttributes_WithDifferentMixedValuesResultsInTwoPossibleTuples() {
  Relation r1 = create("rel1", ("pId":id(),"age":Domain::\int())).v(("pId":key("p1"),"age":term(lit(\int(20))))).build();
  Relation r2 = create("rel2", ("pId":id(),"age":Domain::\int())).v(("pId":key("p1"),"age":term(var("rel2_age", Sort::\int())))).build();

  Relation result = union(r1,r2);

  return result == create("result", ("pId":id(), "age":Domain::\int()))
                     .f(("pId":key("p1"), "age":term(lit(\int(20)))),pvar("rel1_p1"),\true())
                     .f(("pId":key("p1"), "age":term(var("rel2_age",Sort::\int()))),\pvar("rel2_p1"), \true())
                     .build() && checkAllDistinct(result);
}