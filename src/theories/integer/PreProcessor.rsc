module theories::integer::PreProcessor

extend theories::PreProcessor; 

import theories::integer::AST;

import Set;
import List;
import util::Maybe;
import Node;
 
bool isConstant(intLit(_)) = true;

Expr replaceConstants(intLit(int i), void (str, AtomDecl) update, bool (str) exists) {
  if (!exists("_c<i>")) {
    AtomDecl consAtom = atomTheoryAndValue("_c<i>", intTheory(), intExpr(\intLit(i))); 
    update("_C<i>", consAtom);  
  }
  
  return variable("_C<i>");   
} 
 
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

Expr transform(subtraction(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return subtraction(l,r);}, newResultAtom, addRelation, addConstraint, "min", newRelNr)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(addition(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return addition(l,r);}, newResultAtom, addRelation, addConstraint, "plus", newRelNr)
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(multiplication(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(lhs, rhs, Expr (Expr l, Expr r) {return multiplication(l,r);}, newResultAtom, addRelation, addConstraint, "mul", newRelNr)
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

private Expr transform(Expr lhs, Expr rhs, Expr (Expr l, Expr r) operation, str () newResultAtom, void (str, list[AtomDecl], list[list[Atom]], list[list[Atom]]) addRelation, void (AlleFormula) addConstraint, str baseRelName, str () newRelNr) {
  // check arity
  if (size(getOneFrom(lhs@tuples)) != 1 || size(getOneFrom(rhs@tuples)) != 1) {
    throw "Integer arithmetic expression can only be performed on unary relations";
  } 
   
  list[list[Atom]] productResult = [l + r | list[Atom] l <- lhs@tuples, list[Atom] r <- rhs@tuples];
  
  list[AtomDecl] resultAtoms = [];
  list[list[Atom]] upperBound = [];
  
  for (list[Atom] t <- productResult) {
    AtomDecl resultAtom = atomTheoryAndValue("<newResultAtom()>", intTheory(), intExpr(operation(variable(t[0]), variable(t[1]))));
    list[Atom] newTuple = t + resultAtom.atom;
     
    resultAtoms += resultAtom;
    upperBound = upperBound + [newTuple];
  } 
   
  str relNr = newRelNr();
  
  str newResultRelName = "_R_<relNr>";
  str newRelName = "_<baseRelName>_<relNr>";
  
  addRelation(newResultRelName, resultAtoms, [[a.atom] | AtomDecl a <- resultAtoms],[[a.atom] | AtomDecl a <- resultAtoms]);
  addRelation(newRelName, resultAtoms, [], upperBound);
  
  Expr domainLhs = lhs@domain; //simplify(lhs@domain);
  Expr domainRhs = rhs@domain; //simplify(rhs@domain);
       
  addConstraint(subset(variable(newRelName), product(product(domainLhs, domainRhs), variable(newResultRelName))));
  addConstraint(universal([varDecl("a", domainLhs), varDecl("b", domainRhs)], nonEmpty(\join(variable("b"), \join(variable("a"), variable(newRelName))))));
  
  return \join(rhs, \join(lhs, variable(newRelName))[@domain=product(domainRhs, variable(newResultRelName))])[@tuples = [[r.atom] | AtomDecl r <- resultAtoms]][@domain=variable(newResultRelName)]; 
}  

private Expr simplify(Expr expr) {
  return bottom-up visit(expr) {
    case \join(variable(str var), \join(variable(var), Expr other)) => other
    //case \join(variable(str var), product(Expr lhs, Expr rhs)) => rhs when startsWith(var, lhs)
    //case \join(product(Expr lhs, variable(str var)), variable(var)) => lhs
  } 
}

private Expr endsWith(product(Expr _, Expr rhs)) = endsWith(rhs);
private Expr endsWith(j:\join(Expr _, Expr _)) = endsWith(simplify(j));
private Expr endsWith(v:variable(str _)) = v;
private default Expr endsWith(Expr e) = e;

private bool startsWith(str var, product(Expr lhs, Expr _)) = startsWith(var, lhs);
private bool startsWith(str var, variable(var)) = true;
private default bool startsWith(Expr e) = false;
