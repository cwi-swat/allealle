module translation::tests::relationTests::IntersectionTester

import translation::Relation;
import translation::AST;
import translation::tests::relationTests::RelationBuilder;
import smtlogic::Core;

import IO;

test bool unionCompatibleRelationsCanBeIntersected() {
  Relation r1 = create("rel1", ("id":id())).t(("id":lit(id("r1")))).t(("id":lit(id("r2")))).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":lit(id("r2")))).build();
  
  return intersect(r1,r2) == create("result", ("id":id())).t(("id":lit(id("r2")))).build();
}

test bool unionIncompatibleRelationsCannotBeIntersected() {
  Relation r1 = create("rel1", ("id1":id())).t(("id1":lit(id("r1")))).build();
  Relation r2 = create("rel2", ("id2":id())).t(("id2":lit(id("r2")))).build();

  try {
    intersect(r1,r2);
    fail;
  } catch e: ;     
  
  return true;
} 

test bool intersectIsCommutative() {
  Relation r1 = create("rel1", ("id":id())).t(("id":lit(id("r1")))).t(("id":lit(id("r2")))).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":lit(id("r2")))).build();

  return intersect(r1,r2) == intersect(r2,r1);  
}

test bool intersectIsAssociative() {
  Relation r1 = create("rel1", ("id":id())).t(("id":lit(id("r1")))).t(("id":lit(id("r2")))).t(("id":lit(id("r3")))).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":lit(id("r2")))).t(("id":lit(id("r3")))).build();
  Relation r3 = create("rel3", ("id":id())).t(("id":lit(id("r3")))).build();

  return intersect(intersect(r1,r2),r3) == intersect(r1,intersect(r2,r3));  
}

test bool intersectOfDistinctRelationsIsEmpty() {
  Relation r1 = create("rel1", ("id":id())).t(("id":lit(id("r1")))).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":lit(id("r2")))).build();
 
  return intersect(r1,r2) == <r1.heading,(),{"id"}>;  
}

test bool optionalRowsTrumpMandatoryRowsAfterIntersection() {
  Relation r1 = create("rel1", ("id":id())).t(("id":lit(id("r1")))).build();
  Relation r2 = create("rel2", ("id":id())).v(("id":lit(id("r1")))).build();
  
  return intersect(r1,r2) == create("result", ("id":id())).f(("id":lit(id("r1"))), pvar("rel2_r1"),\true()).build();
}

test bool twoOptionalRowsMustBothBePresentAfterIntersection() {
  Relation r1 = create("rel1", ("id":id())).v(("id":lit(id("r1")))).build();
  Relation r2 = create("rel2", ("id":id())).v(("id":lit(id("r1")))).build();
  
  return intersect(r1,r2) == create("result", ("id":id())).f(("id":lit(id("r1"))), \and(pvar("rel1_r1"),pvar("rel2_r1")), \true()).build();
}

test bool intersectOfNAryRelationsIsAllowed() {
  Relation r1 = create("rel1", ("pId":id(),"hId":id())).t(("pId":lit(id("p1")),"hId":lit(id("h1")))).t(("pId":lit(id("p1")),"hId":lit(id("h2")))).build();
  Relation r2 = create("rel2", ("pId":id(),"hId":id())).t(("pId":lit(id("p1")),"hId":lit(id("h1")))).build();

  return intersect(r1,r2) == create("result", ("pId":id(),"hId":id()))
    .t(("pId":lit(id("p1")),"hId":lit(id("h1"))))
    .build();
}