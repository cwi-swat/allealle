module theories::Translator

import logic::Propositional;
import theories::AST;
import theories::Binder;

import IO;
import List;

Environment createInitialEnvironment(Problem p) {
  map[Atom, AtomDecl] atomsWithTheories = (ad.atom : ad | AtomDecl ad <- p.uni.atoms, ad has theory);

  Environment env = (rb.relName:createRelationalMapping(rb, atomsWithTheories) | RelationalBound rb <- p.bounds);
  
  return env;
}
                                                                                                                                                    
RelationMatrix createRelationalMapping(relationalBound(str relName, int arity, list[Tuple] lb, list[Tuple] ub), map[Atom, AtomDecl] atomsWithTheories) {
  str idxToStr(list[Atom] idx) = intercalate("_", idx);
  
  RelationMatrix result = (idx : <\true(), constructTheoryExtensions(idx, atomsWithTheories)> | \tuple(list[Atom] idx) <- lb);
  result += (idx : <var("<relName>_<idxToStr(idx)>"), constructTheoryExtensions(idx, atomsWithTheories)> | \tuple(list[Atom] idx) <- ub, idx notin result);
   
  return result;
} 
                                           
TheoryExtension constructTheoryExtensions(Index idx, map[Atom, AtomDecl] atomsWithTheories) {
  TheoryExtension result = ();
  
  for (int i <- [0..size(idx)], Atom a := idx[i], a in atomsWithTheories) {
    if (atomsWithTheories[a].theory in result) {
      result[atomsWithTheories[a].theory] += constructTheoryExtension(i, atomsWithTheories[a]);
    } else {
      result[atomsWithTheories[a].theory] = constructTheoryExtension(i, atomsWithTheories[a]);
    }
  }
  
  return result;
}

default ExtensionEncoding constructTheoryExtension(int idx, AtomDecl ad) { throw "No theory extension found for theory \'<ad.theory>\'"; } 
                                                                                            
Formula translate(Problem p, Environment env) = (\true() | and(it, r) | AlleFormula f <- p.constraints, Formula r := translateFormula(f, env, p.uni));  

Environment constructSingleton(str newVarName, list[Atom] vector, RelationMatrix origMatrix) = (newVarName : (vector : <\true(), origMatrix[vector].ext>));

Formula translateFormula(empty(Expr expr), Environment env, Universe uni) 
  = \not(translateFormula(nonEmpty(expr), env, uni));

Formula translateFormula(atMostOne(Expr expr), Environment env, Universe uni)   
  = \or(translateFormula(empty(expr), env, uni), translateFormula(exactlyOne(expr), env, uni));

Formula translateFormula(exactlyOne(Expr expr), Environment env, Universe uni) 
  = (\false() | \or(it, \and(m[x].relForm, (\true() | \and(it, \not(m[y].relForm)) | Index y <- m, y != x))) | Index x <- m)    
    when RelationMatrix m := translateExpression(expr, env, uni);
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

Formula translateFormula(nonEmpty(Expr expr), Environment env, Universe uni) = (\false() | \or(it,  m[x].relForm) | Index x <- m)
  when RelationMatrix m := translateExpression(expr, env, uni);
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
  RelationMatrix lhs = translateExpression(lhsExpr, env, uni);
  RelationMatrix rhs = translateExpression(rhsExpr, env, uni);
  
  RelationMatrix m = ();
  for (Index idx <- (lhs + rhs)) {
    Formula lhsVal = (idx in lhs) ? lhs[idx].relForm : \false();
    Formula rhsVal = (idx in rhs) ? rhs[idx].relForm : \false();
 
    m[idx] = <\or(\not(lhsVal), rhsVal), ()>;
    if (m[idx].relForm == \false()) {
      return \false();
    }
  } 

  if (m == ()) {
    return \false();
  }

  Formula result = \true();
  for (Index idx <- m) {
    if (m[idx].relForm == \false()) {
      return \false();
    }
    
    result = \and(result, m[idx].relForm);
  }
  
  return result;
}
     
Formula translateFormula(equal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni)
  = \and(translateFormula(subset(lhsExpr, rhsExpr), env, uni), translateFormula(subset(rhsExpr, lhsExpr), env, uni));

Formula translateFormula(inequal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) 
  = translateFormula(negation(equal(lhsExpr, rhsExpr)), env, uni);
  
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
    
    RelationMatrix m = translateExpression(hd.binding, env + extendedEnvironment, uni);
    for (Index idx <- m) {
      Formula clause = buildOr(tl, extendedEnvironment + constructSingleton(hd.name, idx, m));
    
      if (clause == \false() && m[idx].relForm == \true()) {
        return \false();
      }
      
      result += \or(\not(m[idx].relForm), clause);   
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
  
  RelationMatrix m = translateExpression(hd.binding, env, uni);
  
  for (Index x <- m, m[x].relForm != \false()) {
    AlleFormula f = tl != [] ? existential(tl, form) : form;

    Formula clause = \and(m[x].relForm, translateFormula(f, env + constructSingleton(hd.name, x, m), uni));
    
    if (clause == \true()) { return \true(); }
    clauses += clause;
  }
  
  return \or(clauses);
}

//Formula translateFormula(existential(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni)
//  = \or({\and({m[x], translateFormula(f, env + singletonConstructor.constructSingleton(hd.name, m, x.vector), uni)}) | Index x <- m, x.theory == relTheory(), AlleFormula f := (([] == t) ? form : existential(t, form))}) 
//  when [VarDeclaration hd, *t] := decls,
//       Binding m := translateExpression(hd.binding, env, uni);

default Formula translateFormula(AlleFormula f, Environment env, Universe uni) { throw "Translation of formula \'<f>\' not supported"; }

RelationMatrix translateExpression(variable(str name), Environment env, Universe uni) = env[name];

RelationMatrix translateExpression(transpose(Expr expr), Environment env, Universe uni) = transpose(m)
  when RelationMatrix m := translateExpression(expr, env, uni); 

RelationMatrix translateExpression(closure(Expr expr), Environment env, Universe uni) = transitiveClosure(m, uni)
  when RelationMatrix m := translateExpression(expr, env, uni);
     
RelationMatrix translateExpression(reflexClosure(Expr expr), Environment env, Universe uni) = reflexiveTransitiveClosure(m, uni)
  when RelationMatrix m := translateExpression(expr, env, uni);
    
RelationMatrix translateExpression(union(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = disjunction(lhs,rhs)  
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);
  
RelationMatrix translateExpression(intersection(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = conjunction(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);

RelationMatrix translateExpression(difference(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = difference(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);

RelationMatrix translateExpression(\join(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = \join(lhs, rhs) 
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);

RelationMatrix translateExpression(accessorJoin(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateExpression(\join(rhsExpr, lhsExpr), env, uni);
    
RelationMatrix translateExpression(product(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = product(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni), 
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);

//RelationMatrix translateExpression(ifThenElse(AlleFormula caseForm, Expr thenExpr, Expr elseExpr), Environment env, Universe uni)
//   = (idx:<ite(translatedCase, thenRm[idx].relForm, elseRm[idx].relForm), (t : {\or(\not(translatedCase), thenTe) | Formula thenTe <- thenRm[idx].ext[t]} + {\or(translatedCase, elseTe) | Formula elseTe <- elseRm[idx].ext[t]} | Theory t <- thenRm[idx].ext)> | Index idx <- thenRm)
//  when RelationMatrix thenRm := translateExpression(thenExpr, env, uni),
//       RelationMatrix elseRm := translateExpression(elseExpr, env, uni),
//       Formula translatedCase := translateFormula(caseForm, env, uni);
     
RelationMatrix translateExpression(comprehension(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni) {
  RelationMatrix calculate(Index currentIdx, [], Environment extendedEnv, Formula partialForm, TheoryExtension extension) =
    (currentIdx : <\and(partialForm, translateFormula(form, extendedEnv, uni)), extension>);
  
  RelationMatrix calculate(Index currentIdx, [VarDeclaration hd, *VarDeclaration tl], Environment extendedEnv, Formula partialForm, TheoryExtension partialExtensions) {
    RelationMatrix result = ();
    
    RelationMatrix decl = translateExpression(hd.binding, extendedEnv, uni);
    if (arity(decl) > 1) { throw "Higher order comprehensions are not allowed"; }
    
    for (Index idx <- decl) {
      result += calculate(currentIdx + idx, tl, extendedEnv + constructSingleton(hd.name, idx, decl), \and(partialForm, decl[idx].relForm), productTheoryExtension(size(currentIdx + idx), partialExtensions, decl[idx].ext));
    }
    
    return result;
  }
   
  
  return calculate([], decls, env, \true(), ());
}

default RelationMatrix translateExpression(Expr expr, Environment env, Universe uni) { throw "Translation of expression \'<expr>\' not supported"; }

