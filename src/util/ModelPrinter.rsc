module util::ModelPrinter

import ide::CombinedModelFinder;
import translation::Relation;
import smtlogic::Core;
import smtlogic::Ints;

import List;
import Set;
import IO;
import String;

void printAlleModel(Model m) {
  println(model2Str(m));
}

str model2Str(Model m) 
  = "<for (r <- sortRelations(m.relations)) {><model2Str(r)>
    '<}>";

str model2Str(ModelRelation r) 
  = "<r.name> <model2Str(r.heading)> = {<model2Str(r.tuples)>}";

str model2Str(Heading h)
  = "(<intercalate(", ", ["<name> : <model2Str(h[name])>" | name <- h])>)"; 

str model2Str(list[ModelTuple] tuples)
  = intercalate(", ", [model2Str(t) | t <- tuples]);

str model2Str(ModelTuple t)
  = "\<<intercalate(",", [model2Str(a) | a <- t.attributes])>\>"; 

str model2Str(idAttribute(str _, str id)) = id;
str model2Str(fixedAttribute(str _, Term val)) = model2Str(val);
str model2Str(varAttribute(str _, Term val, str _)) = model2Str(val);

str model2Str(lit(Literal l)) = model2Str(l);
str model2Str(neg(Term t)) = "-<model2Str(t)>";

str model2Str(\int(int i)) = "<i>";

str model2Str(id()) = "id";
str model2Str(intDom()) = "int";

private list[ModelRelation] sortRelations(set[ModelRelation] rels) 
  = sort(toList(rels), bool (ModelRelation r1, ModelRelation r2) {return toLowerCase(r1.name) < toLowerCase(r2.name);});