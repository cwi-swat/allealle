module translation::tests::relationTests::ProductTester

import translation::Relation;
import translation::AST;
import translation::tests::relationTests::RelationBuilder;

import smtlogic::Core;
import smtlogic::Ints;

import IO;

test bool productWithOnlyIdFields() {
  Relation pigeon = create("pigeon",("pid":id())).t(("pid":lit(id("p1")))).t(("pid":lit(id("p2")))).build();
  Relation hole   = create("hole",  ("hid":id())).t(("hid":lit(id("h1")))).t(("hid":lit(id("h2")))).build();
  
  return product(pigeon,hole) == create("nest", ("pid":id(),"hid":id()))
                                   .t(("pid":lit(id("p1")),"hid":lit(id("h1"))))
                                   .t(("pid":lit(id("p1")),"hid":lit(id("h2"))))
                                   .t(("pid":lit(id("p2")),"hid":lit(id("h1"))))
                                   .t(("pid":lit(id("p2")),"hid":lit(id("h2"))))
                                   .build();      
}

test bool productIsCommutative() {
  Relation pigeon = create("pigeon",("pid":id())).t(("pid":lit(id("p1")))).t(("pid":lit(id("p2")))).build();
  Relation hole   = create("hole",  ("hid":id())).t(("hid":lit(id("h1")))).t(("hid":lit(id("h2")))).build();
  
  return product(pigeon,hole) == product(hole,pigeon); 
}

test bool productIsAssociative() {
  Relation pigeon = create("pigeon",("pid":id())).t(("pid":lit(id("p1")))).build();
  Relation hole   = create("hole",  ("hid":id())).t(("hid":lit(id("h1")))).build();
  Relation keeper = create("keeper",("kid":id())).t(("kid":lit(id("k1")))).build();
  
  return product(product(pigeon,hole),keeper) == product(keeper,product(hole,pigeon)); 
}

test bool productIsConditionalIfRowsAreConditional() {
  Relation pigeon = create("pigeon",("pid":id())).v(("pid":lit(id("p1")))).v(("pid":lit(id("p2")))).build();
  Relation hole   = create("hole",  ("hid":id())).t(("hid":lit(id("h1")))).v(("hid":lit(id("h2")))).build();
  
  return product(pigeon,hole) == create("nest", ("pid":id(),"hid":id()))
                                   .f(("pid":lit(id("p1")),"hid":lit(id("h1"))), pvar("pigeon_p1"), \true())
                                   .f(("pid":lit(id("p1")),"hid":lit(id("h2"))), \and(pvar("pigeon_p1"),pvar("hole_h2")), \true())
                                   .f(("pid":lit(id("p2")),"hid":lit(id("h1"))), pvar("pigeon_p2"), \true())
                                   .f(("pid":lit(id("p2")),"hid":lit(id("h2"))), \and(pvar("pigeon_p2"),pvar("hole_h2")), \true())
                                   .build();      
}

test bool productWithExtraAttributes() {
  Relation pigeon = create("pigeon",("pid":id(), "age":Domain::\int())).v(("pid":lit(id("p1")),"age":var("a1",Sort::\int()))).v(("pid":lit(id("p2")),"age":var("a2",Sort::\int()))).build();
  Relation hole   = create("hole",  ("hid":id(), "depth":Domain::\int())).t(("hid":lit(id("h1")),"depth":var("d1",Sort::\int()))).v(("hid":lit(id("h2")),"depth":var("d2",Sort::\int()))).build();

  return product(pigeon,hole) == create("nest", ("pid":id(),"hid":id(),"age":Domain::\int(), "depth":Domain::\int()))
                                   .f(("pid":lit(id("p1")),"hid":lit(id("h1")),"age":var("a1",Sort::\int()),"depth":var("d1",Sort::\int())), pvar("pigeon_p1"), \true())
                                   .f(("pid":lit(id("p1")),"hid":lit(id("h2")),"age":var("a1",Sort::\int()),"depth":var("d2",Sort::\int())), \and(pvar("pigeon_p1"),pvar("hole_h2")), \true())
                                   .f(("pid":lit(id("p2")),"hid":lit(id("h1")),"age":var("a2",Sort::\int()),"depth":var("d1",Sort::\int())), pvar("pigeon_p2"), \true())
                                   .f(("pid":lit(id("p2")),"hid":lit(id("h2")),"age":var("a2",Sort::\int()),"depth":var("d2",Sort::\int())), \and(pvar("pigeon_p2"),pvar("hole_h2")), \true())
                                   .build();      
}