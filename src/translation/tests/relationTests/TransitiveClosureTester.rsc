module translation::tests::relationTests::TransitiveClosureTester

import translation::Relation;
import translation::AST;
import translation::tests::relationTests::RelationBuilder;

import smtlogic::Core;
import smtlogic::Ints;

import IO;

test bool transitiveClosureOfParentRelation() {
  Relation parent = create("parent", ("pId":id(),"cId":id()))
                    .t(("pId":lit(id("j")),"cId":lit(id("l"))))
                    .t(("pId":lit(id("j")),"cId":lit(id("b"))))
                    .t(("pId":lit(id("h")),"cId":lit(id("j"))))
                    .build();
                    
  return transitiveClosure(parent,"pId","cId") ==
          create("parent", ("pId":id(),"cId":id()))
                    .t(("pId":lit(id("j")),"cId":lit(id("l"))))
                    .t(("pId":lit(id("j")),"cId":lit(id("b"))))
                    .t(("pId":lit(id("h")),"cId":lit(id("j"))))
                    .t(("pId":lit(id("h")),"cId":lit(id("l"))))
                    .t(("pId":lit(id("h")),"cId":lit(id("b"))))
                    .build();
}