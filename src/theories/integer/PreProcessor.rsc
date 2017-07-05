module theories::integer::PreProcessor

extend theories::PreProcessor; 

import theories::integer::AST;

import Set;
import List;
import util::Maybe;
import Node;

//@memo
AlleFormula transform(intEqual(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = intEqual(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

//@memo 
AlleFormula transform(intEqual(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = intEqual(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

//@memo
AlleFormula transform(intInequal(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = intInequal(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

//@memo
AlleFormula transform(gt(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = gt(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

//@memo
AlleFormula transform(gte(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = gte(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

//@memo
AlleFormula transform(lt(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = lt(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

//@memo
AlleFormula transform(lte(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = lte(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(minimize(Expr expr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = minimize(transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));


//@memo
Expr transform(intLit(int i), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
  str consRelName = "_C<i>";
  AtomDecl constantAtom = atomTheoryAndValue("_c<i>", intTheory(), intExpr(intLit(i)));
  addRelation(consRelName, {constantAtom}, [[constantAtom.atom]], [[constantAtom.atom]]);

  return variable(consRelName)[@minTuples=[[constantAtom.atom]]][@maxTuples=[[constantAtom.atom]]][@domain=variable(consRelName)];
}
  
//@memo 
Expr transform(subtraction(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return addition(l,neg(r));}, newResultAtom, addRelation, addConstraint, "min", newRelNr)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

////@memo
//Expr transform(addition(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
//  = transform(lhs, rhs, Expr (Expr l,Expr r) {return addition(l,r);}, newResultAtom, addRelation, addConstraint, "plus", newRelNr, useCommutativity = true)
//  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
//       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(neg(Expr expr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = neg(transformedExpr)[@minTuples=transformedExpr@minTuples][@maxTuples=transformedExpr@maxTuples][@domain=transformedExpr@domain]
  when transformedExpr := transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

//@memo
Expr transform(addition(list[Expr] terms), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = transform(transformedTerms, Expr (list[Expr] exprs) {return addition(exprs);}, newResultAtom, addRelation, addConstraint, "plus", newRelNr)
  when list[Expr] transformedTerms := [transform(t, env, uni, newResultAtom, addRelation, addConstraint, newRelNr) | Expr t <- terms];


//@memo
Expr transform(multiplication(list[Expr] terms), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(transformedTerms, Expr (list[Expr] exprs) {return multiplication(exprs);}, newResultAtom, addRelation, addConstraint, "mul", newRelNr)
  when list[Expr] transformedTerms := [transform(t, env, uni, newResultAtom, addRelation, addConstraint, newRelNr) | Expr t <- terms];

//@memo
Expr transform(division(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return division(l,r);}, newResultAtom, addRelation, addConstraint, "div", newRelNr)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

//@memo
Expr transform(modulo(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return modulo(l,r);}, newResultAtom, addRelation, addConstraint, "mod", newRelNr)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

private Expr transform(list[Expr] terms, Expr (list[Expr] operands) operation, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str baseRelName, str () newRelNr) {
  // check arity
  if (Expr t <- terms, size(getOneFrom(t@maxTuples)) != 1) {
    throw "Integer arithmetic expression can only be performed on unary relations";
  } 
  
  set[list[Atom]] buildProductResult([], list[Atom] result) = {result};
    
  default set[list[Atom]] buildProductResult([list[Atom] hd, *list[Atom] tl], list[Atom] resultSoFar) {
    set[list[Atom]] result = {};
    
    for (Atom a <- hd) {
      result += buildProductResult(tl, resultSoFar + a);
    } 
    
    return result; 
  } 

  set[list[Atom]] maxProductResult = buildProductResult([r | Expr e <- terms, list[Atom] r := [a | [Atom a] <- e@maxTuples]], []);;
  
  set[AtomDecl] maxResultAtoms = {};
  list[list[Atom]] upperBound = [];
  
  for (list[Atom] t <- maxProductResult) {
    AtomDecl resultAtom = atomTheoryAndValue("<newResultAtom()>", intTheory(), intExpr(operation([variable(a) | Atom a <- t])));
    list[Atom] newTuple = t + resultAtom.atom;
     
    maxResultAtoms += resultAtom;
    upperBound += [newTuple];
  } 
   
  str relNr = newRelNr();
  
  str newResultRelName = "_R_<relNr>";
  str newRelName = "_<baseRelName>_<relNr>";
   
  addRelation(newResultRelName, maxResultAtoms, [[a.atom] | AtomDecl a <- maxResultAtoms],[[a.atom] | AtomDecl a <- maxResultAtoms]);
  addRelation(newRelName, maxResultAtoms, upperBound, upperBound);
       
  Expr buildJoinExpr([Expr e])                        = \join(e, variable(newRelName)); 
  default Expr buildJoinExpr([Expr hd, *Expr tl])     = \join(hd, buildJoinExpr(tl)); 
  return buildJoinExpr(reverse(terms))[@minTuples = [[r.atom] | AtomDecl r <- maxResultAtoms]][@maxTuples = [[r.atom] | AtomDecl r <- maxResultAtoms]][@domain=variable(newResultRelName)]; 
}

private Expr transform(Expr lhs, Expr rhs, Expr (Expr l, Expr r) operation, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str baseRelName, str () newRelNr) {
  // check arity
  if (size(getOneFrom(lhs@maxTuples)) != 1 || size(getOneFrom(rhs@maxTuples)) != 1) {
    throw "Integer arithmetic expression can only be performed on unary relations";
  } 
   
  set[list[Atom]] maxProductResult = {l + r | list[Atom] l <- lhs@maxTuples, list[Atom] r <- rhs@maxTuples};
  
  set[AtomDecl] maxResultAtoms = {};
  list[list[Atom]] upperBound = [];
  
  for (t:[Atom l, Atom r] <- maxProductResult) {
    AtomDecl resultAtom = atomTheoryAndValue("<newResultAtom()>", intTheory(), intExpr(operation(variable(t[0]), variable(t[1]))));
    list[Atom] newTuple = t + resultAtom.atom;

    maxResultAtoms += resultAtom;
    upperBound += [newTuple];
  } 
   
  str relNr = newRelNr();
  
  str newResultRelName = "_R_<relNr>";
  str newRelName = "_<baseRelName>_<relNr>";
  
  addRelation(newResultRelName, maxResultAtoms, [[a.atom] | AtomDecl a <- maxResultAtoms],[[a.atom] | AtomDecl a <- maxResultAtoms]);
  addRelation(newRelName, maxResultAtoms, upperBound, upperBound);
       
  return \join(rhs, \join(lhs, variable(newRelName)))[@minTuples = [[r.atom] | AtomDecl r <- maxResultAtoms]][@maxTuples = [[r.atom] | AtomDecl r <- maxResultAtoms]][@domain=variable(newResultRelName)]; 
}  

//@memo
Expr transform(sum(Expr e), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
  Expr expr = transform(e, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);
   
  if (size(getOneFrom(expr@maxTuples)) != 1) {
    throw "Summation of none unary relations are not allowed";
  }
  
  int max = size(expr@maxTuples);
  int min = size(expr@minTuples);

  Atom sumResultAtom = newResultAtom();
  str sumRelName = "_sum_<newRelNr()>";

  addRelation(sumRelName, {atomAndTheory("<sumResultAtom>", intTheory())}, [[sumResultAtom]], [[sumResultAtom]]);

  // add as many unary, singleton relations as there are possible elements in the relation
  for (int idx <- [0..max], [Atom a] := expr@maxTuples[idx]) {
    addRelation("_SR_<a>", {}, [[a]], [[a]]);
  } 

  Expr buildSummation(int i) = ifThenElse(subset(variable("e<i>"), expr), variable("e<i>"), intLit(0)) when i == max-1;
  Expr buildSummation(int i) = addition(ifThenElse(subset(variable("e<i>"), expr), variable("e<i>"), intLit(0)), buildSummation(i+1)) when i < max-1;

  addConstraint(universal([varDecl("e<i>", variable("_SR_<a>")) | int i <- [0..max], [Atom a] := expr@maxTuples[i]], intEqual(variable(sumRelName), buildSummation(0))));
  
  return variable(sumRelName)[@minTuples=[[sumResultAtom]]][@maxTuples=[[sumResultAtom]]][@domain=variable(sumRelName)];
}

//@memo
Expr transform(car(Expr e), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
  Expr expr = transform(e, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);
   
  int max = size(expr@maxTuples);
  int min = size(expr@minTuples);
 
  Atom carResultAtom = newResultAtom();
  str carRelName = "_car_<newRelNr()>";

  addRelation(carRelName, {atomAndTheory("<carResultAtom>", intTheory())}, [[carResultAtom]], [[carResultAtom]]);

  // add as many unary, singleton relations as there are possible elements in the relation
  for (int idx <- [0..max], [Atom a] := expr@maxTuples[idx]) {
    addRelation("_SR_<a>", {}, [[a]], [[a]]);
  } 

  Expr buildSummation(int i) = ifThenElse(subset(variable("e<i>"), expr), intLit(1), intLit(0)) when i == max-1;
  Expr buildSummation(int i) = addition(ifThenElse(subset(variable("e<i>"), expr), intLit(1), intLit(0)), buildSummation(i+1)) when i < max-1;

  addConstraint(universal([varDecl("e<i>", variable("_SR_<a>")) | int i <- [0..max], [Atom a] := expr@maxTuples[i]], intEqual(variable(carRelName), buildSummation(0))));

  return variable(carRelName)[@minTuples=[[carResultAtom]]][@maxTuples=[[carResultAtom]]][@domain=variable(carRelName)];
}