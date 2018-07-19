module translation::tests::relationTests::NaturalJoinTester

import translation::Relation;
import translation::AST;
import translation::tests::relationTests::RelationBuilder;

import smtlogic::Core;
import smtlogic::Ints;

import IO;

test bool natJoinWithIdFieldsAndNonConditionalRows() {
  Relation nest = create("nest", ("pid":id(),"hid":id())).t(("pid":lit(id("p1")),"hid":lit(id("h1"))))
                                                         .t(("pid":lit(id("p1")),"hid":lit(id("h2"))))
                                                         .t(("pid":lit(id("p2")),"hid":lit(id("h1"))))
                                                         .t(("pid":lit(id("p2")),"hid":lit(id("h2"))))
                                                         .build();
                                                         
  Relation pigeon = create("pigeon", ("pid":id())).t(("pid":lit(id("p1")))).build();
  
  return naturalJoin(nest,pigeon) == create("result", ("pid":id(),"hid":id())).t(("pid":lit(id("p1")),"hid":lit(id("h1"))))
                                                                              .t(("pid":lit(id("p1")),"hid":lit(id("h2"))))
                                                                              .build();
}

test bool natJoinWithIdFieldsAndConditionalRows() {
  Relation nest = create("nest", ("pid":id(),"hid":id())).v(("pid":lit(id("p1")),"hid":lit(id("h1"))))
                                                         .v(("pid":lit(id("p1")),"hid":lit(id("h2"))))
                                                         .v(("pid":lit(id("p2")),"hid":lit(id("h1"))))
                                                         .v(("pid":lit(id("p2")),"hid":lit(id("h2"))))
                                                         .build();
                                                         
  Relation pigeon = create("pigeon", ("pid":id())).v(("pid":lit(id("p1")))).build();
  
  return naturalJoin(nest,pigeon) == create("result", ("pid":id(),"hid":id())).f(("pid":lit(id("p1")),"hid":lit(id("h1"))), \and(pvar("nest_h1_p1"),pvar("pigeon_p1")), \true())
                                                                              .f(("pid":lit(id("p1")),"hid":lit(id("h2"))), \and(pvar("nest_h2_p1"),pvar("pigeon_p1")), \true())
                                                                              .build();
}

test bool natJoinIsCommutative() {
  Relation nest = create("nest", ("pid":id(),"hid":id())).v(("pid":lit(id("p1")),"hid":lit(id("h1"))))
                                                         .v(("pid":lit(id("p1")),"hid":lit(id("h2"))))
                                                         .v(("pid":lit(id("p2")),"hid":lit(id("h1"))))
                                                         .v(("pid":lit(id("p2")),"hid":lit(id("h2"))))
                                                         .build();
                                                         
  Relation pigeon = create("pigeon", ("pid":id())).v(("pid":lit(id("p1")))).build();

  return naturalJoin(nest,pigeon) == naturalJoin(pigeon,nest);
}

test bool natJoinWorksAsFilter() {
  Relation nest = create("nest", ("pid":id(),"hid":id())).v(("pid":lit(id("p1")),"hid":lit(id("h1"))))
                                                         .v(("pid":lit(id("p1")),"hid":lit(id("h2"))))
                                                         .v(("pid":lit(id("p2")),"hid":lit(id("h1"))))
                                                         .v(("pid":lit(id("p2")),"hid":lit(id("h2"))))
                                                         .build();
                                                         
  Relation pigeon = create("pigeon", ("pid":id())).v(("pid":lit(id("p1")))).build();
  Relation hole = create("hole", ("hid":id())).v(("hid":lit(id("h2")))).build();
  
  return naturalJoin(naturalJoin(nest,pigeon),hole) == 
          create("result", ("pid":id(),"hid":id())).f(("pid":lit(id("p1")),"hid":lit(id("h2"))), \and({pvar("nest_h2_p1"),pvar("pigeon_p1"),pvar("hole_h2")}), \true()).build();
}

test bool natJoinIsAssociative() {
  Relation nest = create("nest", ("pid":id(),"hid":id())).v(("pid":lit(id("p1")),"hid":lit(id("h1"))))
                                                         .v(("pid":lit(id("p1")),"hid":lit(id("h2"))))
                                                         .v(("pid":lit(id("p2")),"hid":lit(id("h1"))))
                                                         .v(("pid":lit(id("p2")),"hid":lit(id("h2"))))
                                                         .build();
                                                         
  Relation pigeon = create("pigeon", ("pid":id())).v(("pid":lit(id("p1")))).build();
  Relation hole = create("hole", ("hid":id())).v(("hid":lit(id("h2")))).build();
  
  return naturalJoin(naturalJoin(nest,pigeon),hole) == naturalJoin(pigeon,naturalJoin(nest,hole)); 
}

test bool natJoinOnFixedAttributes() {
  Relation pigeon = create("pigeon", ("pid":id(),"age":Domain::\int())).v(("pid":lit(id("p1")), "age":lit(\int(10)))).build();
  Relation hole = create("hole", ("hid":id(),"age":Domain::\int())).v(("hid":lit(id("h1")), "age":lit(\int(10)))).v(("hid":lit(id("h2")), "age":lit(\int(20)))).build();
  
  return naturalJoin(pigeon,hole) ==
         create("result", ("pid":id(),"hid":id(),"age":Domain::\int()))
           .f(("pid":lit(id("p1")),"hid":lit(id("h1")),"age":lit(\int(10))), \and(pvar("pigeon_p1"),pvar("hole_h1")), \true()).build();
}

test bool natJoinOnOpenAttributes() {
  Relation pigeon = create("pigeon", ("pid":id(),"age":Domain::\int())).v(("pid":lit(id("p1")), "age":var("a1",Sort::\int()))).build();
  Relation hole = create("hole", ("hid":id(),"age":Domain::\int())).v(("hid":lit(id("h1")), "age":var("b1",Sort::\int()))).v(("hid":lit(id("h2")), "age":var("b2",Sort::\int()))).build();
  
  return naturalJoin(pigeon,hole) ==
         create("result", ("pid":id(),"hid":id(),"age":Domain::\int()))
           .f(("pid":lit(id("p1")),"hid":lit(id("h1")),"age":var("b1",Sort::\int())), \and(pvar("pigeon_p1"),pvar("hole_h1")), \equal(var("a1",Sort::\int()),var("b1",Sort::\int())))
           .f(("pid":lit(id("p1")),"hid":lit(id("h2")),"age":var("b2",Sort::\int())), \and(pvar("pigeon_p1"),pvar("hole_h2")), \equal(var("a1",Sort::\int()),var("b2",Sort::\int())))
           .build();
}
