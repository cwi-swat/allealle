module translation::tests::relationTests::EnvironmentTester

import translation::Environment;
import translation::AST;
import translation::Relation;

import smtlogic::Core;

import IO;
import util::Maybe;
import List; 

test bool createEnvironmentFromPreciseDefinedIdTuples() {
  RelationDef simpleRel = relation("simple", [header("id",id())], exact([tup([idd("id1")]),tup([idd("id2")])]));
  
  Problem p = problem([simpleRel], [], nothing(), nothing());
  
  Environment env = createInitialEnvironment(p);
  return env.relations["simple"] == <("id":id()), 
                                     (("id":lit(id("id1"))):<\true(),\true()>, 
                                      ("id":lit(id("id2"))):<\true(),\true()>), 
                                     {"id"}>;
}

test bool createEnvironmentFromPreciseDefinedIdTuplesWithLowerAndUpperBounds() {
  RelationDef simpleRel = relation("simple", [header("id",id())], atLeastAtMost([tup([idd("id1")])],[tup([idd("id1")]), tup([idd("id2")])]));
  
  Problem p = problem([simpleRel], [], nothing(), nothing());
  
  Environment env = createInitialEnvironment(p);
  
  return env.relations["simple"] == <("id":id()), 
                                     (("id":lit(id("id1"))):<\true(),\true()>, 
                                      ("id":lit(id("id2"))):<pvar("simple_id2"),\true()>), 
                                     {"id"}>; 
}

test bool createEnvironmentFromPreciseDefinedIdTuplesWithUpperBounds() {
  RelationDef simpleRel = relation("simple", [header("id",id())], atLeastAtMost([],[tup([idd("id1")]), tup([idd("id2")])]));
  
  Problem p = problem([simpleRel], [], nothing(), nothing());
  
  Environment env = createInitialEnvironment(p);
  return env.relations["simple"] == <("id":id()), 
                                     (("id":lit(id("id1"))):<pvar("simple_id1"),\true()>, 
                                     ("id":lit(id("id2"))):<pvar("simple_id2"),\true()>), 
                                     {"id"}>;
}

test bool createEnvironmentFromRangeDefinedIdTuplesWithUpperBounds() {
  RelationDef simpleRel = relation("simple", [header("id",id())], atLeastAtMost([],[range([id("id",1)], [id("id",3)])]));
  
  Problem p = problem([simpleRel], [], nothing(), nothing());
  
  Environment env = createInitialEnvironment(p);
  return env.relations["simple"] == <("id":id()), 
                                     (("id":lit(id("id1"))):<pvar("simple_id1"),\true()>, 
                                      ("id":lit(id("id2"))):<pvar("simple_id2"),\true()>, 
                                      ("id":lit(id("id3"))):<pvar("simple_id3"),\true()>), 
                                     {"id"}> &&
         toSet(env.idDomain) == {"id1","id2","id3"};
}