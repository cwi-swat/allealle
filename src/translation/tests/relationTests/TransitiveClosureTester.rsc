module translation::tests::relationTests::TransitiveClosureTester

import translation::Relation;
import translation::AST;
import translation::tests::relationTests::RelationBuilder;

import smtlogic::Core;
import smtlogic::Ints;

import IO;

test bool transitiveClosureOfParentRelation() {
  Relation parent = create("parent", ("pId":id(),"cId":id()))
                    .t(("pId":key("j"),"cId":key("l")))
                    .t(("pId":key("j"),"cId":key("b")))
                    .t(("pId":key("h"),"cId":key("j")))
                    .build();
                    
  return transitiveClosure(parent,"pId","cId") ==
          create("parent", ("pId":id(),"cId":id()))
                    .t(("pId":key("j"),"cId":key("l")))
                    .t(("pId":key("j"),"cId":key("b")))
                    .t(("pId":key("h"),"cId":key("j")))
                    .t(("pId":key("h"),"cId":key("l")))
                    .t(("pId":key("h"),"cId":key("b")))
                    .build();;
}