module theories::integer::tests::PreProcessorTest

import theories::integer::AST;
import theories::integer::PreProcessor;

import IO;

private AtomDecl ao(str atom) = atomAndTheory(atom, intTheory());
private Tuple t(Atom atom) = \tuple([atom]);
private Tuple t(Atom a, Atom b, Atom c) = \tuple([a,b,c]);

test bool relationsWithFixedTuplesAlsoHaveAFixedExpressionRelation() {
  Universe uni = universe([ao("n1"),ao("n2"),ao("n3"),ao("n4")]);
  list[RelationalBound] rbs = [relationalBound("A",1,[t("n1"), t("n2")], [t("n1"), t("n2")]),
                               relationalBound("B",1,[t("n3"), t("n4")], [t("n3"), t("n4")])];
                               
  list[AlleFormula] constraints = [gt(addition(variable("A"), variable("B")), intLit(10))];
  
  Problem p = problem(uni, rbs, constraints);
  
  Problem augmentedP = preprocess(p);
  
  if (relationalBound("_plus_1", 3, list[Tuple] lb, list[Tuple] ub) <- augmentedP.bounds) { 
    return lb == ub;
  } 
  
  throw "Unable to locate added relation for original addition expression";
}

test bool relationsWithDifferentLowerAndUpperBoundsHaveAPartiallyFixedExpressionRelation() {
  Universe uni = universe([ao("n1"),ao("n2"),ao("n3"),ao("n4")]);
  list[RelationalBound] rbs = [relationalBound("A",1,[t("n1")], [t("n1"), t("n2")]),
                               relationalBound("B",1,[t("n3")], [t("n3"), t("n4")])];
                               
  list[AlleFormula] constraints = [gt(addition(variable("A"), variable("B")), intLit(10))];
  
  Problem p = problem(uni, rbs, constraints);
  
  Problem augmentedP = preprocess(p);
  
  if (relationalBound("_plus_1", 3, list[Tuple] lb, list[Tuple] ub) <- augmentedP.bounds) { 
    return lb == [t("n1","n3","_r1")];
  } 
  
  throw "Unable to locate added relation for original addition expression";

}

test bool relationsWithDifferentLowerAndUpperBoundsCanHaveEmptyFixedExpressionRelation() {
  Universe uni = universe([ao("n1"),ao("n2"),ao("n3"),ao("n4")]);
  list[RelationalBound] rbs = [relationalBound("A",1,[t("n1"), t("n2")], [t("n1"), t("n2")]),
                               relationalBound("B",1,[], [t("n3"), t("n4")])];
                               
  list[AlleFormula] constraints = [gt(addition(variable("A"), variable("B")), intLit(10))];
  
  Problem p = problem(uni, rbs, constraints);
  
  Problem augmentedP = preprocess(p);
    
  if (relationalBound("_plus_1", 3, list[Tuple] lb, list[Tuple] ub) <- augmentedP.bounds) { 
    return lb == [];
  } 
  
  throw "Unable to locate added relation for original addition expression";
}

test bool relationsWithNoLowerBoundsAlwaysHaveEmptyFixedExpressionRelation() {
  Universe uni = universe([ao("n1"),ao("n2"),ao("n3"),ao("n4")]);
  list[RelationalBound] rbs = [relationalBound("A",1,[], [t("n1"), t("n2")]),
                               relationalBound("B",1,[], [t("n3"), t("n4")])];
                               
  list[AlleFormula] constraints = [gt(addition(variable("A"), variable("B")), intLit(10))];
  
  Problem p = problem(uni, rbs, constraints);
  
  Problem augmentedP = preprocess(p);
    
  if (relationalBound("_plus_1", 3, list[Tuple] lb, list[Tuple] ub) <- augmentedP.bounds) { 
    return lb == [];
  } 
  
  throw "Unable to locate added relation for original addition expression";
}