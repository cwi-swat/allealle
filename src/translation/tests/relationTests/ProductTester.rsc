module translation::tests::relationTests::ProductTester

import translation::Relation;
import translation::AST;
import translation::tests::relationTests::RelationBuilder;

import smtlogic::Core;
import smtlogic::Ints;

import IO;

test bool productWithOnlyIdFields() {
  Relation pigeon = create("pigeon",("pid":id())).t(("pid":key("p1"))).t(("pid":key("p2"))).build();
  Relation hole   = create("hole",  ("hid":id())).t(("hid":key("h1"))).t(("hid":key("h2"))).build();
  
  return product(pigeon,hole) == create("nest", ("pid":id(),"hid":id()))
                                   .t(("pid":key("p1"),"hid":key("h1")))
                                   .t(("pid":key("p1"),"hid":key("h2")))
                                   .t(("pid":key("p2"),"hid":key("h1")))
                                   .t(("pid":key("p2"),"hid":key("h2")))
                                   .build();      
}

test bool productIsCommutative() {
  Relation pigeon = create("pigeon",("pid":id())).t(("pid":key("p1"))).t(("pid":key("p2"))).build();
  Relation hole   = create("hole",  ("hid":id())).t(("hid":key("h1"))).t(("hid":key("h2"))).build();
  
  return product(pigeon,hole) == product(hole,pigeon); 
}

test bool productIsAssociative() {
  Relation pigeon = create("pigeon",("pid":id())).t(("pid":key("p1"))).build();
  Relation hole   = create("hole",  ("hid":id())).t(("hid":key("h1"))).build();
  Relation keeper = create("keeper",("kid":id())).t(("kid":key("k1"))).build();
  
  return product(product(pigeon,hole),keeper) == product(keeper,product(hole,pigeon)); 
}

test bool productIsConditionalIfRowsAreConditional() {
  Relation pigeon = create("pigeon",("pid":id())).v(("pid":key("p1"))).v(("pid":key("p2"))).build();
  Relation hole   = create("hole",  ("hid":id())).t(("hid":key("h1"))).v(("hid":key("h2"))).build();
  
  return product(pigeon,hole) == create("nest", ("pid":id(),"hid":id()))
                                   .f(("pid":key("p1"),"hid":key("h1")), pvar("pigeon_p1"), \true())
                                   .f(("pid":key("p1"),"hid":key("h2")), \and(pvar("pigeon_p1"),pvar("hole_h2")), \true())
                                   .f(("pid":key("p2"),"hid":key("h1")), pvar("pigeon_p2"), \true())
                                   .f(("pid":key("p2"),"hid":key("h2")), \and(pvar("pigeon_p2"),pvar("hole_h2")), \true())
                                   .build();      
}

test bool productWithExtraAttributes() {
  Relation pigeon = create("pigeon",("pid":id(), "age":Domain::\int())).v(("pid":key("p1"),"age":term(var("a1",Sort::\int())))).v(("pid":key("p2"),"age":term(var("a2",Sort::\int())))).build();
  Relation hole   = create("hole",  ("hid":id(), "depth":Domain::\int())).t(("hid":key("h1"),"depth":term(var("d1",Sort::\int())))).v(("hid":key("h2"),"depth":term(var("d2",Sort::\int())))).build();

  return product(pigeon,hole) == create("nest", ("pid":id(),"hid":id(),"age":Domain::\int(), "depth":Domain::\int()))
                                   .f(("pid":key("p1"),"hid":key("h1"),"age":term(var("a1",Sort::\int())),"depth":term(var("d1",Sort::\int()))), pvar("pigeon_p1"), \true())
                                   .f(("pid":key("p1"),"hid":key("h2"),"age":term(var("a1",Sort::\int())),"depth":term(var("d2",Sort::\int()))), \and(pvar("pigeon_p1"),pvar("hole_h2")), \true())
                                   .f(("pid":key("p2"),"hid":key("h1"),"age":term(var("a2",Sort::\int())),"depth":term(var("d1",Sort::\int()))), pvar("pigeon_p2"), \true())
                                   .f(("pid":key("p2"),"hid":key("h2"),"age":term(var("a2",Sort::\int())),"depth":term(var("d2",Sort::\int()))), \and(pvar("pigeon_p2"),pvar("hole_h2")), \true())
                                   .build();      
}