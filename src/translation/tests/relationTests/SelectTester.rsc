module translation::tests::relationTests::SelectTester

import translation::Relation;
import translation::AST;
import translation::tests::relationTests::RelationBuilder;

import smtlogic::Core;
import smtlogic::Ints;

import IO;

Formula mustBeOlderThen18(Tuple tup) = gt(tup["age"], lit(\int(18)));

test bool selectAddsConstraintsOnAttributes() {
  Relation r = create("person", ("id":id(),"age":Domain::\int()))
                .t(("id":lit(id("p1")),"age":var("a1",Sort::\int())))
                .build();
                
  return select(r,mustBeOlderThen18) == create("person", ("id":id(),"age":Domain::\int()))
                                          .f(("id":lit(id("p1")),"age":var("a1",Sort::\int())), \true(), gt(var("a1",Sort::\int()),lit(\int(18))))
                                          .build();                
}

test bool selectFiltersIfFalse() {
  Relation r = create("person", ("id":id(),"age":Domain::\int()))
                .t(("id":lit(id("p1")),"age":lit(\int(17))))
                .build();
                
  return select(r,mustBeOlderThen18) == create("person", ("id":id(),"age":Domain::\int()))
                                          .build();                

}

test bool selectDoesNothingIfFilterIsMet() {
  Relation r = create("person", ("id":id(),"age":Domain::\int()))
                .t(("id":lit(id("p1")),"age":lit(\int(19))))
                .build();
                
  return select(r,mustBeOlderThen18) == r;                
}

test bool selectFailsWhenAttributeDoesNotExist() {
  Relation r = create("person", ("id":id()))
                .t(("id":lit(id("p1"))))
                .build();

  try {
    select(r,mustBeOlderThen18);
    fail;
  } catch e: ;
  
  return true;
}
