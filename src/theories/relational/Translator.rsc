module theories::relational::Translator

extend theories::Translator; 

import theories::relational::AST;
import theories::relational::Binder;

import logic::Propositional;

import IO;
import List; 
import Map;
import Set;
  
Binding createRelationalMapping(relationalBound(str relName, int arity, list[Tuple] lowerBounds, list[Tuple] upperBounds)) =
  createRelationalMapping(relationalBoundWithTheory(relName, relTheory(), arity, lowerBounds, upperBounds));

Binding createRelationalMapping(relationalBoundWithTheory(str relName, relTheory(), int arity, list[Tuple] lb, list[Tuple] ub)) {
  str idxToStr(list[Atom] idx) = intercalate("_", idx);
  
  Binding result = (<relTheory(), idx> : \true() | \tuple(list[Atom] idx) <- lb);
  result += (<relTheory(), idx> : var("<relName>_<idxToStr(idx)>") | \tuple(list[Atom] idx) <- ub, <relTheory(), idx> notin result);
   
  return result;
} 

Formula translateFormula(empty(Expr expr), Environment env, Universe uni) 
  = \not(translateFormula(nonEmpty(expr), env, uni));

Formula translateFormula(atMostOne(Expr expr), Environment env, Universe uni)   
  = \or(translateFormula(empty(expr), env, uni), translateFormula(exactlyOne(expr), env, uni));

Formula translateFormula(exactlyOne(Expr expr), Environment env, Universe uni) 
  = (\false() | \or(it, \and(m[x], (\true() | \and(it, \not(m[y])) | Index y <- m, y.theory == relTheory(), y != x))) | Index x <- m, x.theory == relTheory())    
    when Binding m := translateExpression(expr, env, uni);
//{
//  Binding m = translateExpression(expr, env, uni);
//
//  Formula orClause = \false();
//  for (Index x <- m, x.theory == relTheory(), m[x] != \false()) {
//    Formula innerAndClause = m[x];
//    
//    for (Index y <- m, y.theory == relTheory(), y != x) { 
//
//      if (m[y] == \true()) {
//        innerAndClause = \false();
//        break;
//      }
//      
//      innerAndClause = \and(innerAndClause, \not(m[y]));
//    }
//    
//    if (innerAndClause == \true()) {
//      return \true();
//    } 
//    
//    orClause = \or(orClause, and(m[x],innerAndClause));
//  }
//  
//  println("result one = <orClause>");
//  
//  return orClause;
//}

Formula translateFormula(nonEmpty(Expr expr), Environment env, Universe uni)      
  = (\false() | \or(it,  m[x]) | Index x <- m, x.theory == relTheory())
  when Binding m := translateExpression(expr, env, uni);
//{
//  Binding m = translateExpression(expr, env, uni);
//  
//  Formula orClause = \false();
//  for (Index x <- m, x.theory == relTheory(), m[x] != \false()) {
//    if (m[x] == \true()) {
//      return \true();
//    }
//    
//    orClause = or(orClause, m[x]);
//  }
//  
//  return orClause;
//}


Formula translateFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) 
  //= m == () ? \false() : (\true() | \and(it, m[x]) | Index x <- m, x.theory == relTheory())
  //when Binding lhs := translateExpression(lhsExpr, env, uni),
  //   Binding rhs := translateExpression(rhsExpr, env, uni),
  //   Binding m :=(idx:\or({\not(lhsVal), rhsVal}) | Index idx <- (lhs + rhs), idx.theory == relTheory(), Formula lhsVal := ((idx in lhs) ? lhs[idx] : \false()), Formula rhsVal := ((idx in rhs) ? rhs[idx] : \false())); 
{
  Binding lhs = translateExpression(lhsExpr, env, uni);
  Binding rhs = translateExpression(rhsExpr, env, uni);
  
  Binding m = ();
  for (Index idx <- (lhs + rhs), idx.theory == relTheory()) {
    Formula lhsVal = (idx in lhs) ? lhs[idx] : \false();
    Formula rhsVal = (idx in rhs) ? rhs[idx] : \false();
 
    m[idx] = \or(\not(lhsVal), rhsVal);
    if (m[idx] == \false()) {
      return \false();
    }
  } 

  if (m == ()) {
    return \false();
  }

  Formula result = \true();
  for (Index idx <- m) {
    if (m[idx] == \false()) {
      return \false();
    }
    
    result = \and(result, m[idx]);
  }
  
  return result;
}
     
Formula translateFormula(equal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni)
  = \and(translateFormula(subset(lhsExpr, rhsExpr), env, uni), translateFormula(subset(rhsExpr, lhsExpr), env, uni));
  
Formula translateFormula(negation(AlleFormula form), Environment env, Universe uni) 
  = \not(translateFormula(form, env, uni));
  
Formula translateFormula(conjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni)
  = \and(translateFormula(lhsForm, env, uni), translateFormula(rhsForm, env, uni));
  
Formula translateFormula(disjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni)
  = \or(translateFormula(lhsForm, env, uni), translateFormula(rhsForm, env, uni));
  
Formula translateFormula(implication(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni)
  = \or(\not(translateFormula(lhsForm, env, uni)), translateFormula(rhsForm, env, uni));
  
Formula translateFormula(equality(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni)
  = \or(\and(translateFormula(lhsForm, env, uni),  translateFormula(rhsForm, env, uni)), \and(\not(translateFormula(lhsForm, env, uni)), \not(translateFormula(rhsForm, env, uni))));

data Formula 
  = substitutes(Environment subs)
  ; 

Formula translateFormula(universal(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni) 
{
  Formula buildOr([], Environment extendedEnvironment) = substitutes(extendedEnvironment);

  Formula buildOr([VarDeclaration hd, *VarDeclaration tl], Environment extendedEnvironment) {
    set[Formula] result = {};
    
    Binding m = translateExpression(hd.binding, env, uni);
    for (Index idx <- m, idx.theory == relTheory()) {
      extendedEnvironment["<hd.name>"] = (<relTheory(), idx.vector>:\true());
      Formula clause = buildOr(tl, extendedEnvironment);
    
      if (clause == \false() && m[idx] == \true()) {
        return \false();
      }
      
      result += \or(\not(m[idx]), clause);   
    }    
    
    return \and(result);
  }
  
  Formula result = buildOr(decls, ());
  result = visit(result) {
    case substitutes(Environment subs) => translateFormula(form, env + subs, uni)
  }
  
  return result;
}
  //= \and({\or({\not(m[x]), translateFormula(f, env + singletonConstructor.constructSingleton(hd.name, m, x.vector), uni)}) | Index x <- m, x.theory == relTheory(), AlleFormula f := (([] == t) ? form : universal(t, form))})
  //when [VarDeclaration hd, *t] := decls,
  //     Binding m := translateExpression(hd.binding, env, uni);
   
Formula translateFormula(existential(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni) {
  set[Formula] clauses = {};
    
  VarDeclaration hd = decls[0];
  list[VarDeclaration] tl = (size(decls) > 1) ? decls[1..] : [];
  
  Binding m = translateExpression(hd.binding, env, uni);
  
  for (Index x <- m, x.theory == relTheory(), m[x] != \false()) {
    AlleFormula f = tl != [] ? existential(tl, form) : form;

    Formula clause = \and({m[x], translateFormula(f, env + constructSingleton(hd.name, x.vector, m), uni)});
    
    if (clause == \true()) { return \true(); }
    clauses += clause;
  }
  
  return \or(clauses);
}

//Formula translateFormula(existential(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni)
//  = \or({\and({m[x], translateFormula(f, env + singletonConstructor.constructSingleton(hd.name, m, x.vector), uni)}) | Index x <- m, x.theory == relTheory(), AlleFormula f := (([] == t) ? form : existential(t, form))}) 
//  when [VarDeclaration hd, *t] := decls,
//       Binding m := translateExpression(hd.binding, env, uni);

Binding constructSingletonWithTheory(relTheory(), list[Atom] vector, Formula originalValue) = (<relTheory(), vector>:\true()); 

Binding translateExpression(variable(str name), Environment env, Universe uni) = env[name];

Binding translateExpression(transpose(Expr expr), Environment env, Universe uni) = transpose(m)
  when Binding m := translateExpression(expr, env, uni); 

Binding translateExpression(closure(Expr expr), Environment env, Universe uni) = transitiveClosure(m, uni)
  when Binding m := translateExpression(expr, env, uni);
     
Binding translateExpression(reflexClosure(Expr expr), Environment env, Universe uni) = reflexiveTransitiveClosure(m, uni)
  when Binding m := translateExpression(expr, env, uni);
    
Binding translateExpression(union(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = disjunction(lhs,rhs)  
  when Binding lhs := translateExpression(lhsExpr, env, uni),
       Binding rhs := translateExpression(rhsExpr, env, uni);
  
Binding translateExpression(intersection(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = conjunction(lhs, rhs)
  when Binding lhs := translateExpression(lhsExpr, env, uni),
       Binding rhs := translateExpression(rhsExpr, env, uni);

Binding translateExpression(difference(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = 
  (x:\and(lhs[x],rhsVal) | Index x <- lhs, x.theory == relTheory(), Formula rhsVal := ((x notin rhs) ? \true() : \not(rhs[x])))
  when Binding lhs := translateExpression(lhsExpr, env, uni),
       Binding rhs := translateExpression(rhsExpr, env, uni);

Binding translateExpression(\join(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = \join(lhs, rhs) 
  when Binding lhs := translateExpression(lhsExpr, env, uni),
       Binding rhs := translateExpression(rhsExpr, env, uni);

Binding translateExpression(accessorJoin(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateExpression(\join(rhsExpr, lhsExpr), env, uni);
    
Binding translateExpression(product(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = product(lhs, rhs)
  when Binding lhs := translateExpression(lhsExpr, env, uni),
       Binding rhs := translateExpression(rhsExpr, env, uni);

Binding translateExpression(ifThenElse(AlleFormula caseForm, Expr thenExpr, Expr elseExpr), Environment env, Universe uni)
   = (idx:ite(translateFormula(caseForm, env, uni),p[idx],q[idx]) | Index idx <- p)
  when Binding p := translateExpression(thenExpr, env, uni),
       Binding q := translateExpression(elseExpr, env, uni);
     
Binding translateExpression(comprehension(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni) {
  list[tuple[str,Binding]] varBindings = [];
  
  for (VarDeclaration decl <- decls) {
    Binding b = translateExpression(decl.binding, env, uni);
    if (arity(b) > 1) { throw "Can not have higher order comprehensions"; }
    varBindings += <decl.name, b>; 
  } 
  
  Binding calculate(list[Atom] curVector, [<str name, Binding last>], Environment extendedEnv, Formula partialFormula) = 
    (<relTheory(), curVector + idx.vector> : \and(partialFormula, translateFormula(form, extendedEnv + constructSingleton(name, idx.vector, last), uni)) | Index idx <- last, idx.theory == relTheory());
   
  default Binding calculate(list[Atom] curVector, [<str name, Binding next>, *tuple[str,Binding] tl], Environment extendedEnv, Formula partialFormula) {
    Binding result = (); 
    
    for (Index idx <- next, idx.theory == relTheory()) {
      result += calculate(curVector + idx.vector, tl, extendedEnv + constructSingleton(name, idx.vector, next), \and(partialFormula, next[idx]));  
    }
    
    return result;
  } 
  
  return calculate([], varBindings, env, \true());
}