module translation::tests::relationTests::RenameTester

import translation::Relation;
import translation::AST;
import translation::tests::relationTests::RelationBuilder;

import smtlogic::Core;
import smtlogic::Ints;

import IO;

test bool renameWithSameNamesIsIsomorphic() {
  Relation r = create("rel", ("id":id(),"att":Domain::\int())).t(("id":key("r1"), "att":term(lit(\int(10))))).t(("id":key("r2"), "att":term(lit(\int(10))))).build();
  
  return rename(r, ("att":"att", "id":"id")) == r;
}

test bool renameAllAttributes() {
  Relation r = create("rel", ("id":id(),"att":Domain::\int())).t(("id":key("r1"), "att":term(lit(\int(10))))).t(("id":key("r2"), "att":term(lit(\int(10))))).build();
    
  return rename(r, ("att":"att2", "id":"id2")) == create("rel", ("id2":id(),"att2":Domain::\int()))
                                                    .t(("id2":key("r1"), "att2":term(lit(\int(10)))))
                                                    .t(("id2":key("r2"), "att2":term(lit(\int(10))))).build();
}

test bool renameSomeAttributes() {
  Relation r = create("rel", ("id1":id(),"id2":id(),"att":Domain::\int()))
                .t(("id1":key("r1"), "id2":key("rr1"), "att":term(lit(\int(10)))))
                .t(("id1":key("r2"), "id2":key("rr2"), "att":term(lit(\int(10)))))
                .build();
                
  return rename(r, ("id1":"id")) == create("rel", ("id":id(),"id2":id(),"att":Domain::\int()))
                                      .t(("id":key("r1"), "id2":key("rr1"), "att":term(lit(\int(10)))))
                                      .t(("id":key("r2"), "id2":key("rr2"), "att":term(lit(\int(10)))))
                                      .build();                
}

test bool renameAllAttributesMustHaveDistinctNames() {
  Relation r = create("rel", ("id1":id(),"id2":id())).t(("id1":key("r1"), "id2":key("r2"))).build();

  try {
    rename(r, ("id1":"id2"));
    fail;
  } catch e: ;
  
  return true;
}

test bool renameAllAttributesMustExist() {
  Relation r = create("rel", ("id":id(),"att":Domain::\int())).t(("id":key("r1"), "att":term(lit(\int(10))))).t(("id":key("r2"), "att":term(lit(\int(10))))).build();

  try {
    rename(r, ("nonexisting":"att"));
    fail;
  } catch e: ;
  
  return true;
}