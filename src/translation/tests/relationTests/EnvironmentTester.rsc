module translation::tests::relationTests::EnvironmentTester

import translation::Environment;
import translation::AST;
import translation::Relation;

import smtlogic::Core;

import IO;

test bool createEnvironmentFromPreciseDefinedIdTuples() {
  RelationDef simpleRel = relation("simple", [header("id",id())], exact([tup([id("id1")]),tup([id("id2")])]));
  
  Problem p = problem([simpleRel], []);
  
  Environment env = createInitialEnvironment(p);
  return env == <("simple": <("id":id()), 
                            (("id":key("id1")):<\true(),\true()>, 
                             ("id":key("id2")):<\true(),\true()>), 
                             {"id"}>), 
                 ["id1","id2"]>; 
}

test bool createEnvironmentFromPreciseDefinedIdTuplesWithLowerAndUpperBounds() {
  RelationDef simpleRel = relation("simple", [header("id",id())], atLeastAtMost([tup([id("id1")])],[tup([id("id1")]), tup([id("id2")])]));
  
  Problem p = problem([simpleRel], []);
  
  Environment env = createInitialEnvironment(p);
  return env == <("simple": <("id":id()), 
                            (("id":key("id1")):<\true(),\true()>, 
                             ("id":key("id2")):<pvar("simple_id2"),\true()>), 
                             {"id"}>), 
                 ["id1","id2"]>; 

}

test bool createEnvironmentFromPreciseDefinedIdTuplesWithUpperBounds() {
  RelationDef simpleRel = relation("simple", [header("id",id())], atLeastAtMost([],[tup([id("id1")]), tup([id("id2")])]));
  
  Problem p = problem([simpleRel], []);
  
  Environment env = createInitialEnvironment(p);
  return env == <("simple": <("id":id()), 
                            (("id":key("id1")):<pvar("simple_id1"),\true()>, 
                             ("id":key("id2")):<pvar("simple_id2"),\true()>), 
                             {"id"}>), 
                 ["id1","id2"]>; 
}

test bool createEnvironmentFromRangeDefinedIdTuplesWithUpperBounds() {
  RelationDef simpleRel = relation("simple", [header("id",id())], atLeastAtMost([],[range([id("id",1)], [id("id",3)])]));
  
  Problem p = problem([simpleRel], []);
  
  Environment env = createInitialEnvironment(p);
  return env == <("simple": <("id":id()), 
                            (("id":key("id1")):<pvar("simple_id1"),\true()>, 
                             ("id":key("id2")):<pvar("simple_id2"),\true()>, 
                             ("id":key("id3")):<pvar("simple_id3"),\true()>), 
                             {"id"}>), 
                 ["id1","id2","id3"]>; 
}

test bool createEnvironmentFromPreciseDefinedMixedAttributes() {
}