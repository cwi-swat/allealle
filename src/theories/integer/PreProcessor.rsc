module theories::integer::PreProcessor

extend theories::PreProcessor; 

import theories::integer::AST;

import Set;
import List;
import util::Maybe;
import Node;

AlleFormula transform(intEqual(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = intEqual(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));
 
AlleFormula transform(intEqual(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = intEqual(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(intInequal(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = intInequal(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(gt(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = gt(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(gte(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = gte(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(lt(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = lt(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(lte(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = lte(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

Expr transform(intLit(int i), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
  str consRelName = "_C<i>";
  AtomDecl constantAtom = atomTheoryAndValue("_c<i>", intTheory(), intExpr(intLit(i)));
  addRelation(consRelName, [constantAtom], [[constantAtom.atom]], [[constantAtom.atom]]);

  return variable(consRelName)[@minTuples=[[constantAtom.atom]]][@maxTuples=[[constantAtom.atom]]][@domain=variable(consRelName)];
}

Expr transform(subtraction(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return addition(l,neg(r));}, newResultAtom, addRelation, addConstraint, "min", newRelNr, useCommutativity = true)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(addition(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return addition(l,r);}, newResultAtom, addRelation, addConstraint, "plus", newRelNr, useCommutativity = true)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(multiplication(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return multiplication(l,r);}, newResultAtom, addRelation, addConstraint, "mul", newRelNr, useCommutativity = true)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(division(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return division(l,r);}, newResultAtom, addRelation, addConstraint, "div", newRelNr)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(modulo(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return modulo(l,r);}, newResultAtom, addRelation, addConstraint, "mod", newRelNr)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

private Expr transform(Expr lhs, Expr rhs, Expr (Expr l, Expr r) operation, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str baseRelName, str () newRelNr, bool useCommutativity = false) {
  // check arity
  if (size(getOneFrom(lhs@maxTuples)) != 1 || size(getOneFrom(rhs@maxTuples)) != 1) {
    throw "Integer arithmetic expression can only be performed on unary relations";
  } 
   
  list[list[Atom]] minProductResult = [l + r | list[Atom] l <- lhs@minTuples, list[Atom] r <- rhs@minTuples];
  list[list[Atom]] maxProductResult = [l + r | list[Atom] l <- lhs@maxTuples, list[Atom] r <- rhs@maxTuples];
  
  list[AtomDecl] minResultAtoms = [];
  list[AtomDecl] maxResultAtoms = [];
  list[list[Atom]] lowerBound = [];
  list[list[Atom]] upperBound = [];
  
  for (t:[Atom l, Atom r] <- maxProductResult, !useCommutativity || !([r, l, Atom _] <- upperBound)) {
    AtomDecl resultAtom = atomTheoryAndValue("<newResultAtom()>", intTheory(), intExpr(operation(variable(t[0]), variable(t[1]))));
    list[Atom] newTuple = t + resultAtom.atom;
     
    if (t in minProductResult) {
      minResultAtoms += resultAtom;
      lowerBound += [newTuple];
    }
    maxResultAtoms += resultAtom;
    upperBound += [newTuple];
  } 
   
  str relNr = newRelNr();
  
  str newResultRelName = "_R_<relNr>";
  str newRelName = "_<baseRelName>_<relNr>";
  
  addRelation(newResultRelName, maxResultAtoms, [[a.atom] | AtomDecl a <- maxResultAtoms],[[a.atom] | AtomDecl a <- maxResultAtoms]);
  addRelation(newRelName, maxResultAtoms, lowerBound, upperBound);
  
  Expr domainLhs = lhs@domain;
  Expr domainRhs = rhs@domain;
       
  addConstraint(subset(variable(newRelName), product(product(domainLhs, domainRhs), variable(newResultRelName))));
  if (useCommutativity) { 
    addConstraint(universal([varDecl("a", domainLhs), varDecl("b", domainRhs)], disjunction(nonEmpty(\join(variable("b"), \join(variable("a"), variable(newRelName)))), nonEmpty(\join(variable("a"), \join(variable("b"), variable(newRelName)))) )));
  } else {
    addConstraint(universal([varDecl("a", domainLhs), varDecl("b", domainRhs)], nonEmpty(\join(variable("b"), \join(variable("a"), variable(newRelName))))));
  }
    
  return \join(rhs, \join(lhs, variable(newRelName))[@domain=product(domainRhs, variable(newResultRelName))])[@minTuples = [[r.atom] | AtomDecl r <- minResultAtoms]][@maxTuples = [[r.atom] | AtomDecl r <- maxResultAtoms]][@domain=variable(newResultRelName)]; 
}  

Expr transform(sum(Expr e), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
   Expr expr = transform(e, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);
   
   if (size(getOneFrom(expr@maxTuples)) != 1) {
    throw "Summation of none unary relations are not allowed";
  }
  
  int max = size(expr@maxTuples);
  int min = size(expr@minTuples);
 
  Atom sumResultAtom = newResultAtom();
  str sumRelName = "_sum_<newRelNr()>";
  
  Expr buildSummation(int i) = variable("r<i>") when i == 0;
  Expr buildSummation(int i) = addition(variable("r<i>"), buildSummation(i-1)) when i > 0;
  
  Expr buildUnion(int i) = variable("r<i>") when i == 0;
  Expr buildUnion(int i) = union(variable("r<i>"), buildUnion(i-1)) when i > 0;  
  
  Expr buildDomain(int i) = expr@domain when i == 0;
  Expr buildDomain(int i) = difference(expr@domain, buildUnion(i-1)) when i > 0;  
  
  //AlleFormula buildForAll(int iter) = universal([varDecl("r<i>", buildDomain(i)) | int i <- [(max-min)..iter], i < iter-1] + [varDecl("r<iter-1>", buildDomain(iter-1))], implication(empty(difference(expr@domain, buildUnion(iter-1))), intEqual(buildSummation(iter-1), variable(sumRelName)))) when iter == max; 
  AlleFormula buildConstraint(int iter) = implication(empty(expr@domain), intEqual(variable(sumRelName), intLit(0))) when iter == 0;
  default AlleFormula buildConstraint(int iter) = universal([varDecl("r<i>", buildDomain(i)) | int i <- [0..iter]], implication(empty(difference(expr@domain, buildUnion(iter-1))), intEqual(buildSummation(iter-1), variable(sumRelName))));
   
  addRelation(sumRelName, [atomAndTheory("<sumResultAtom>", intTheory())], [[sumResultAtom]], [[sumResultAtom]]);
  
  for (int i <- [min..max+1]) {
    addConstraint(buildConstraint(i));
  }
  
  return variable(sumRelName)[@minTuples=[[sumResultAtom]]][@maxTuples=[[sumResultAtom]]][@domain=variable(sumRelName)];
}

Expr transform(car(Expr e), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
  Expr expr = transform(e, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);
   
  int max = size(expr@maxTuples);
  int min = size(expr@minTuples);
 
  Atom carResultAtom = newResultAtom();
  str carRelName = "_car_<newRelNr()>";
  
  Expr buildUnion(int i) = variable("r<i>") when i == 0;
  Expr buildUnion(int i) = union(variable("r<i>"), buildUnion(i-1)) when i > 0;  
  
  Expr buildDomain(int i) = expr@domain when i == 0;
  Expr buildDomain(int i) = difference(expr@domain, buildUnion(i-1)) when i > 0;  
  
  AlleFormula buildConstraint(int iter) = implication(empty(expr@domain), intEqual(variable(carRelName), intLit(0))) when iter == 0;
  default AlleFormula buildConstraint(int iter) = universal([varDecl("r<i>", buildDomain(i)) | int i <- [0..iter]], implication(empty(difference(expr@domain, buildUnion(iter-1))), intEqual(variable(carRelName), intLit(iter)))); 
   
  addRelation(carRelName, [atomAndTheory("<carResultAtom>", intTheory())], [[carResultAtom]], [[carResultAtom]]);
  
  if (min==max) {
    addConstraint(intEqual(variable(carRelName), intLit(max)));
  } else {
    for (int i <- [min..max+1]) {
      addConstraint(buildConstraint(i));
    }
  }
  
  
  return variable(carRelName)[@minTuples=[[carResultAtom]]][@maxTuples=[[carResultAtom]]][@domain=variable(carRelName)];
}