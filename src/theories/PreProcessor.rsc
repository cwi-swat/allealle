module theories::PreProcessor

import theories::AST;
   
import List;
import IO;
import Set;
import util::Maybe;
import Node;
import theories::integer::Unparser;

 
private alias Env = map[str relName, set[list[AtomDecl]] maxTuples];

anno set[list[AtomDecl]] Expr@maxTuples;

Problem preprocess(Problem problem) {
  int lastResult = 0;
  str newResultAtom() { 
    lastResult += 1;
    return "_r<lastResult>";
  }
  
  set[AtomDecl] newAtoms = {};
  list[RelationalBound] newRelations = [];
  list[AlleFormula] newConstraints = [];
  Env env = buildEnv(problem);
    
  void addRelation(str relName, set[AtomDecl] atomDecls, set[list[AtomDecl]] maxTuples) {
    newAtoms += atomDecls;
    
    list[Tuple] newBounds = [\tuple([ad.atom | AtomDecl ad <- tup]) | list[AtomDecl] tup <- maxTuples];
    
    if (r:relationalBound(relName, int arity, list[Tuple] lb, list[Tuple] ub) <- newRelations) {
      newRelations -= r;
      newRelations += relationalBound(relName, arity, lb + newBounds, ub + newBounds);
      
      env[relName] += maxTuples;
    }
    else {
      int arity = size(getOneFrom(maxTuples));
   
      newRelations += [relationalBound(relName, arity, newBounds, newBounds)];
      
      env[relName] = maxTuples;
    }
  }  
  
  void addConstraint(AlleFormula newForm) {
    newConstraints += newForm;
  }
  
  int lastId = 0;
  
  str newRelNr() {
    lastId += 1;
    return "<lastId>";
  }  
 
  list[AlleFormula] transformedForms = [transform(f, env, problem.uni, newResultAtom, addRelation, addConstraint, newRelNr) | AlleFormula f <- problem.constraints];

  while (newConstraints != []) {
    Problem temp = problem;
    temp.uni.atoms += toList(newAtoms);
    temp.bounds += newRelations;
    temp.constraints = transformedForms + newConstraints;
   
    writeFile(|project://allealle/examples/intermediate_transformation.alle|, unparse(temp));
    
    for (AlleFormula f <- newConstraints) {
      newConstraints -= f;
      transformedForms += transform(f, env, problem.uni, newResultAtom, addRelation, addConstraint, newRelNr);
    }
  }
  
  problem.uni.atoms += toList(newAtoms);
  problem.bounds += newRelations;
  problem.constraints = transformedForms + newConstraints;
  
  problem = delAnnotations(problem);
    
  return problem;
}

data Expr = emptyExpr(); 

Env buildEnv(Problem p) {
  AtomDecl findAtomDecl(Atom a, str _) = ad when AtomDecl ad <- p.uni.atoms, ad.atom == a;  
  default AtomDecl findAtomDecl(Atom a, str relName) { throw "Unable to locate atom declaration \'<a>\' referenced in relation \'<relName>\'"; }
  
  Env env = ();
  
  for (RelationalBound rb <- p.bounds) {
    env[rb.relName] = {[findAtomDecl(a, rb.relName) | Atom a <- t.atoms] | Tuple t <- rb.upperBounds};
  }

  return env;
}

AlleFormula transform(empty(Expr expr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = empty(transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(atMostOne(Expr expr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = atMostOne(transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));   

AlleFormula transform(exactlyOne(Expr expr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = exactlyOne(transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(nonEmpty(Expr expr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = nonEmpty(transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(subset(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = subset(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(equal(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = equal(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(inequal(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = inequal(transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(negation(AlleFormula form), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = negation(transform(form, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(conjunction(AlleFormula lhsForm, AlleFormula rhsForm), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = conjunction(transform(lhsForm, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsForm, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(disjunction(AlleFormula lhsForm, AlleFormula rhsForm), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = disjunction(transform(lhsForm, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsForm, env, uni, newResultAtom, addRelation, addConstraint, newRelNr)); 

AlleFormula transform(implication(AlleFormula lhsForm, AlleFormula rhsForm), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = implication(transform(lhsForm, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsForm, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(equality(AlleFormula lhsForm, AlleFormula rhsForm), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = equality(transform(lhsForm, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), transform(rhsForm, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(universal(list[VarDeclaration] decls, AlleFormula form), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
  bool addToEnv(str name, set[list[AtomDecl]] maxTuples) {
    env += (name : maxTuples);
    return true; 
  }
  
  decls = top-down visit(decls) {
    case varDecl(str name, Expr binding) => varDecl(name, e) when Expr e := transform(binding, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), addToEnv(name, e@maxTuples)
  }
  
  return universal(decls, transform(form, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));
} 

AlleFormula transform(existential(list[VarDeclaration] decls, AlleFormula form), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
  bool addToEnv(str name, set[list[AtomDecl]] maxTuples) {
    env += (name : maxTuples);
    return true;
  }
  
  decls = top-down visit(decls) {
    case varDecl(str name, Expr binding) => varDecl(name, e) when Expr e := transform(binding, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), addToEnv(name, e@maxTuples)
  }
  
  return existential(decls, transform(form, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));
}
default AlleFormula transform(AlleFormula f, Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) { throw "transformer for formula \'<f>\' not supported"; }

Expr transform(variable(str name), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = variable(name)[@maxTuples=env[name]];

Expr transform(attributeLookup(Expr expr, str name), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
  // lookup act as a filter on the attributes. Result is a list with atom declarations with only one attribute
  
  Expr e = transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);
  
  set[list[AtomDecl]] newMaxTuples = {};
  for (list[AtomDecl] old <- e@maxTuples) {
    list[AtomDecl] new = [atomWithAttributes(a, [at]) | atomWithAttributes(Atom a, list[Attribute] attributes) <- old, Attribute at <- attributes, at.name == name];
    newMaxTuples += new;
  }  
  
  return attributeLookup(e, name)[@maxTuples=newMaxTuples];
} 

Expr transform(transpose(Expr expr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transpose(e)[@maxTuples={reverse(t) | list[AtomDecl] t <- e@maxTuples}] 
  when Expr e := transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr); 

private set[list[AtomDecl]] square(set[list[AtomDecl]] tuples, int i, int sizeOfUniverse, Env env) = tuples when i >= sizeOfUniverse;
private default set[list[AtomDecl]] square(set[list[AtomDecl]] tuples, int i, int sizeOfUniverse, Env env) = \join(tuples, square(tuples, i*2, sizeOfUniverse, env)); 

Expr transform(closure(Expr expr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = closure(e)[@maxTuples=square(e@maxTuples, 1, size(uni.atoms), env)] 
  when Expr e := transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr); 

private set[list[AtomDecl]] identity(set[list[AtomDecl]] orig) = {[a | AtomDecl a <- vector, int i <- [0..arity]] | list[AtomDecl] vector <- orig} when int arity := size(getOneFrom(orig));

Expr transform(reflexClosure(Expr expr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = reflexClosure(e)[@maxTuples = identity(e@maxTuples) + square(e@maxTuples, 1, size(uni.atoms), env)] 
  when Expr e := transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);
  
Expr transform(union(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = union(lhs,rhs)[@maxTuples = lhs@maxTuples + rhs@maxTuples] 
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), 
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);  

Expr transform(intersection(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = intersection(lhs, rhs)[@maxTuples = lhs@maxTuples & rhs@maxTuples] 
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), 
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(difference(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = difference(lhs, rhs)[@maxTuples = lhs@maxTuples] 
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), 
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(\join(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = \join(lhs, rhs)[@maxTuples = \join(lhs@maxTuples, rhs@maxTuples)] 
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), 
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

set[list[AtomDecl]] \join(set[list[AtomDecl]] lhs, set[list[AtomDecl]] rhs) = {hd + tl | [*AtomDecl hd, AtomDecl last] <- lhs, [AtomDecl first, *AtomDecl tl] <- rhs, last.atom == first.atom};  

Expr transform(accessorJoin(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = transform(\join(rhsExpr, lhsExpr), env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(product(Expr lhsExpr, Expr rhsExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = product(lhs, rhs)[@maxTuples = {l + r | list[AtomDecl] l <- lhs@maxTuples, list[AtomDecl] r <- rhs@maxTuples}]
  when Expr lhs := transform(lhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr rhs := transform(rhsExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);

Expr transform(ifThenElse(AlleFormula caseForm, Expr thenExpr, Expr elseExpr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) 
  = ifThenElse(transform(caseForm, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), th, el)[@maxTuples=th@maxTuples + el@maxTuples]
  when Expr th := transform(thenExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr),
       Expr el := transform(elseExpr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr); 

Expr transform(comprehension(list[VarDeclaration] decls, AlleFormula form), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
  set[list[AtomDecl]] compMaxTuples = {};
  
  bool addToEnv(str name, set[list[AtomDecl]] maxTuples) {
    env += (name : maxTuples);
    compMaxTuples += maxTuples;
    return true;
  }
  
  decls = top-down visit(decls) {
    case varDecl(str name, Expr binding) => varDecl(name, e) when Expr e := transform(binding, env, uni, newResultAtom, addRelation, addConstraint, newRelNr), addToEnv(name, e@maxTuples)
  }
  
  return comprehension(decls, transform(form, env, uni, newResultAtom, addRelation, addConstraint, newRelNr))[@maxTuples=compMaxTuples];
}

default Expr transform(Expr expr, Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) { throw "Unable to transform expression \'<expr>\'"; }
