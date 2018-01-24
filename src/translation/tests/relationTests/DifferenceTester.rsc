module translation::tests::relationTests::DifferenceTester

import translation::Relation;
import translation::AST;
import translation::tests::relationTests::RelationBuilder;

import smtlogic::Core;
import smtlogic::Ints;

import IO;

test bool unionCompatibleRelationsCanBeDifferenced() {
  Relation r1 = create("rel1", ("id":id())).t(("id":key("r1"))).t(("id":key("r2"))).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":key("r2"))).build();
  
  return difference(r1,r2) == create("result", ("id":id())).t(("id":key("r1"))).build();
}

test bool unionIncompatibleRelationsCannotBeDifferenced() {
  Relation r1 = create("rel1", ("id1":id())).t(("id1":key("r1"))).build();
  Relation r2 = create("rel2", ("id2":id())).t(("id2":key("r2"))).build();

  try {
    difference(r1,r2);
    fail;
  } catch e: ;     
  
  return true;
}

test bool differenceIsNotCommutative() {
  Relation r1 = create("rel1", ("id":id())).t(("id":key("r1"))).t(("id":key("r2"))).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":key("r2"))).build();

  return difference(r1,r2) != difference(r2,r1);  
}

test bool intersectionIsNotAssociative() {
  Relation r1 = create("rel1", ("id":id())).t(("id":key("r1"))).t(("id":key("r2"))).t(("id":key("r3"))).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":key("r2"))).t(("id":key("r3"))).build();
  Relation r3 = create("rel3", ("id":id())).t(("id":key("r3"))).build();

  return difference(difference(r1,r2),r3) != difference(r1,difference(r2,r3));  
}

test bool differenceOfDistinctRelationsResultsInTheLeftRelations() {
  Relation r1 = create("rel1", ("id":id())).t(("id":key("r1"))).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":key("r2"))).build();

  return difference(r1,r2) == r1;  
}

test bool differenceOnAnEmptyRelationResultInAnEmptyRelation() {
  Relation r1 = create("rel1", ("id":id())).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":key("r2"))).build();

  return difference(r1,r2) == r1;  
}

test bool differenceWithAnEmptyRelationResultsInTheOriginalRelation() {
  Relation r1 = create("rel1", ("id":id())).t(("id":key("r1"))).build();
  Relation r2 = create("rel2", ("id":id())).build();

  return difference(r1,r2) == r1;  
}

test bool optionalRowsTrumpMandatoryRows() {
  Relation r1 = create("rel1", ("id":id())).t(("id":key("r1"))).build();
  Relation r2 = create("rel2", ("id":id())).v(("id":key("r1"))).build();
  
  return difference(r1,r2) == create("result", ("id":id())).f(("id":key("r1")), not(pvar("rel2_r1")), \true()).build();
}

test bool optionalRowsTrumpMandatoryRowsPartTwo() {
  Relation r1 = create("rel1", ("id":id())).v(("id":key("r1"))).build();
  Relation r2 = create("rel2", ("id":id())).t(("id":key("r1"))).build();
  
  return difference(r1,r2) == create("result", ("id":id())).build();
}

test bool onEqualRows_rowOfRhsRelationMustNotExists() {
  Relation r1 = create("rel1", ("id":id())).v(("id":key("r1"))).build();
  Relation r2 = create("rel2", ("id":id())).v(("id":key("r1"))).build();
  
  return difference(r1,r2) == create("result", ("id":id())).f(("id":key("r1")), \and(pvar("rel1_r1"),not(pvar("rel2_r1"))), \true()).build();
}

test bool differenceOfNonOptionalRowsMustHaveExactSameAttributeValues() {
  Relation r1 = create("rel1", ("id":id(),"num":Domain::\int())).t(("id":key("r1"),"num":term(lit(\int(10))))).build();
  Relation r2 = create("rel2", ("id":id(),"num":Domain::\int())).t(("id":key("r1"),"num":term(lit(\int(10))))).build();
  
  return difference(r1,r2) == create("result", ("id":id(),"num":Domain::\int())).build();
}

test bool differenceOfRowsMustHaveExactSameAttributeValues() {
  Relation r1 = create("rel1", ("id":id(),"num":Domain::\int())).v(("id":key("r1"),"num":term(lit(\int(20))))).build();
  Relation r2 = create("rel2", ("id":id(),"num":Domain::\int())).v(("id":key("r1"),"num":term(lit(\int(10))))).build();
  
  return difference(r1,r2) == create("result", ("id":id(),"num":Domain::\int())).f(("id":key("r1"),"num":term(lit(\int(20)))), pvar("rel1_r1"), \true()).build();
}

test bool differenceOfRowsMustHaveExactSameAttributeValuesAlsoWhenTheyAreVariable() {
  Relation r1 = create("rel1", ("id":id(),"num":Domain::\int())).v(("id":key("r1"),"num":term(var("n1",Sort::\int())))).build();
  Relation r2 = create("rel2", ("id":id(),"num":Domain::\int())).v(("id":key("r1"),"num":term(var("n2",Sort::\int())))).build();
  
  return difference(r1,r2) == create("result", ("id":id(),"num":Domain::\int())).f(("id":key("r1"),"num":term(var("n1",Sort::\int()))), pvar("rel1_r1"), \or(not(pvar("rel2_r1")),not(equal(var("n1",Sort::\int()),var("n2",Sort::\int()))))).build();
}


test bool differenceOfOptionalRowsMustHaveExactSameAttributeValues() {
  Relation r1 = create("rel1", ("id":id(),"num":Domain::\int())).v(("id":key("r1"),"num":term(lit(\int(10))))).build();
  Relation r2 = create("rel2", ("id":id(),"num":Domain::\int())).v(("id":key("r1"),"num":term(lit(\int(10))))).build();
  
  return difference(r1,r2) == create("result", ("id":id(),"num":Domain::\int())).f(("id":key("r1"),"num":term(lit(\int(10)))), \and(pvar("rel1_r1"),not(pvar("rel2_r1"))), \true()).build();
}