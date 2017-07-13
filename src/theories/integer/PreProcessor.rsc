module theories::integer::PreProcessor

extend theories::PreProcessor; 

import theories::integer::AST;

import Set;
import List;
import util::Maybe;
import Node;

AlleFormula transform(intEqual(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = intEqual(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(intEqual(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = intEqual(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(intInequal(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = intInequal(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(gt(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = gt(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(gte(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = gte(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(lt(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = lt(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(lte(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = lte(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

Expr transform(intLit(int i), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
  str consRelName = "_C<i>";
  AtomDecl constantAtom = atomWithAttributes("_c<i>", [attributeAndValue("cons", intTheory(), intExpr(intLit(i)))]);
  
  addRelation(consRelName, {constantAtom}, {[constantAtom]});

  return attributeLookup(variable(consRelName), "cons")[@maxTuples={[constantAtom]}];
}
  
Expr transform(subtraction(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return addition(l,neg(r));}, newResultAtom, addRelation, addConstraint, "min", newRelNr)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(neg(Expr expr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = neg(transformedExpr)[@maxTuples=transformedExpr@maxTuples]
  when transformedExpr := transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(addition(list[Expr] terms), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = transform(transformedTerms, Expr (list[Expr] exprs) {return addition(exprs);}, newResultAtom, addRelation, addConstraint, "plus", newRelNr)
  when list[Expr] transformedTerms := [transform(t, env, uni, newResultAtom, addRelation, addConstraint, newRelNr) | Expr t <- terms];


Expr transform(multiplication(list[Expr] terms), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(transformedTerms, Expr (list[Expr] exprs) {return multiplication(exprs);}, newResultAtom, addRelation, addConstraint, "mul", newRelNr)
  when list[Expr] transformedTerms := [transform(t, env, uni, newResultAtom, addRelation, addConstraint, newRelNr) | Expr t <- terms];

Expr transform(division(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return division(l,r);}, newResultAtom, addRelation, addConstraint, "div", newRelNr)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(modulo(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return modulo(l,r);}, newResultAtom, addRelation, addConstraint, "mod", newRelNr)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

private Expr getAttributeExpr(Atom a, attributeAndValue(str name, Theory _, intExpr(i:intLit(_)))) = i;
private default Expr getAttributeExpr(Atom a, Attribute at) = attributeLookup(variable(a), at.name);

private Expr transform(list[Expr] terms, Expr (list[Expr] operands) operation, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str baseRelName, str () newRelNr) {
  // check arity
  if (Expr t <- terms, list[AtomDecl] l <- t@maxTuples, size(l) != 1) {
    println(t);
    iprintln(l);

    throw "Integer arithmetic expression can only be performed on unary relations with an integer attribute selected";
  }
  
  set[list[AtomDecl]] buildProductResult([], list[AtomDecl] result) = {result};
    
  default set[list[AtomDecl]] buildProductResult([list[AtomDecl] hd, *list[AtomDecl] tl], list[AtomDecl] resultSoFar) {
    set[list[AtomDecl]] result = {};
    
    for (AtomDecl ad <- hd) {
      result += buildProductResult(tl, resultSoFar + ad);
    } 
    
    return result; 
  } 

  set[list[AtomDecl]] maxProductResult = buildProductResult([r | Expr e <- terms, list[AtomDecl] r := [ad | [AtomDecl ad] <- e@maxTuples]], []);
  
  set[AtomDecl] resultAtoms = {};
  set[list[AtomDecl]] upperBound = {};
  
  for (list[AtomDecl] t <- maxProductResult) {
    AtomDecl resultAtom = atomWithAttributes("<newResultAtom()>", [attributeAndValue("val", intTheory(), intExpr(operation([getAttributeExpr(a, at) | atomWithAttributes(Atom a, [Attribute at]) <- t])))]);
    list[AtomDecl] newTuple = t + resultAtom;
     
    resultAtoms += resultAtom;
    upperBound += newTuple;
  } 
   
  str relNr = newRelNr();
  
  str newRelName = "_<baseRelName>_<relNr>";
   
  addRelation(newRelName, resultAtoms, upperBound);
       
  Expr buildJoinExpr([Expr e])                        = \join(e, variable(newRelName)); 
  default Expr buildJoinExpr([Expr hd, *Expr tl])     = \join(hd, buildJoinExpr(tl)); 
  
  return attributeLookup(buildJoinExpr(reverse(terms)), "val")[@maxTuples = {[r | AtomDecl r <- resultAtoms]}]; 
}

private Expr transform(Expr lhs, Expr rhs, Expr (Expr l, Expr r) operation, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str baseRelName, str () newRelNr) {
  if (list[AtomDecl] l <- lhs@maxTuples + rhs@maxTuples, size(l) != 1) {
    throw "Integer arithmetic expression can only be performed on unary relations with an integer attribute selected";
  } 
   
  set[list[AtomDecl]] maxProductResult = {l + r | list[AtomDecl] l <- lhs@maxTuples, list[AtomDecl] r <- rhs@maxTuples};
  
  set[AtomDecl] resultAtoms = {};
  set[list[AtomDecl]] upperBound = {};
  
  for (t:[atomWithAttributes(Atom l,[Attribute atLhs]), atomWithAttributes(Atom r,[Attribute atRhs])] <- maxProductResult) {
    AtomDecl resultAtom = atomWithAttributes("<newResultAtom()>", [attributeAndValue("val", intTheory(), intExpr(operation(getAttributeExpr(l, atLhs), getAttributeExpr(r, atRhs))))]);
    list[AtomDecl] newTuple = t + resultAtom;

    resultAtoms += resultAtom;
    upperBound += newTuple;
  } 
   
  str relNr = newRelNr();
  str newRelName = "_<baseRelName>_<relNr>";
  
  addRelation(newRelName, resultAtoms, upperBound);
       
  return attributeLookup(\join(rhs, \join(lhs, variable(newRelName))), "val")[@maxTuples = {[r | AtomDecl r <- resultAtoms]}]; 
}  

Expr transform(sum(attributeLookup(Expr e, str name)), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
  Expr expr = transform(e, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);
   
  if (list[AtomDecl] ad := getOneFrom(expr@maxTuples), size(ad) != 1) {
    throw "Summation of none unary relations are not allowed";
  }
  
  int max = size(expr@maxTuples);

  AtomDecl sumResultAtom = atomWithAttributes(newResultAtom(), [attribute("val", intTheory())]);
  str sumRelName = "_sum_<newRelNr()>";

  addRelation(sumRelName, {sumResultAtom}, {[sumResultAtom]});

  // add as many unary, singleton relations as there are possible elements in the relation
  for ([AtomDecl ad] <- expr@maxTuples) {
    addRelation("_SR_<ad.atom>", {}, {[ad]});
  } 

  Expr buildSummation(int i) = ifThenElse(subset(variable("e<i>"), expr), attributeLookup(variable("e<i>"), name), intLit(0)) when i == max-1;
  Expr buildSummation(int i) = addition(ifThenElse(subset(variable("e<i>"), expr), attributeLookup(variable("e<i>"), name), intLit(0)), buildSummation(i+1)) when i < max-1;

  addConstraint(universal([varDecl("e<i>", variable("_SR_<ad.atom>")) | int i <- [0..max], [AtomDecl ad] := toList(expr@maxTuples)[i]], intEqual(variable(sumRelName), buildSummation(0))));
  
  return attributeLookup(variable(sumRelName), "val")[@maxTuples={[sumResultAtom]}];
}

//@memo
Expr transform(car(Expr e), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
  Expr expr = transform(e, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);
   
  int max = size(expr@maxTuples);
 
  AtomDecl carResultAtom = atomWithAttributes(newResultAtom(), [attribute("val", intTheory())]);
  str carRelName = "_car_<newRelNr()>";

  addRelation(carRelName, {carResultAtom}, {[carResultAtom]});

  // add as many unary, singleton relations as there are possible elements in the relation
  for ([AtomDecl ad] <- expr@maxTuples) {
    addRelation("_CR_<ad.atom>", {}, {[ad]});
  } 

  Expr buildSummation(int i) = ifThenElse(subset(variable("e<i>"), expr), intLit(1), intLit(0)) when i == max-1;
  Expr buildSummation(int i) = addition(ifThenElse(subset(variable("e<i>"), expr), intLit(1), intLit(0)), buildSummation(i+1)) when i < max-1;

  addConstraint(universal([varDecl("e<i>", variable("_CR_<ad.atom>")) | int i <- [0..max], [AtomDecl ad] := toList(expr@maxTuples)[i]], intEqual(variable(carRelName), buildSummation(0))));

  return attributeLookup(variable(carRelName), "val")[@maxTuples={[carResultAtom]}];
}