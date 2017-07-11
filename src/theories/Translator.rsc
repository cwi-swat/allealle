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
  
  RelationMatrix result = (idx : <\true(), constructTheoryExtensions(relName, \true(), idx, atomsWithTheories)> | \tuple(list[Atom] idx) <- lb);
  result += (idx : <var, constructTheoryExtensions(relName, var, idx, atomsWithTheories)> | \tuple(list[Atom] idx) <- ub, idx notin result, Formula var := var("<relName>_<idxToStr(idx)>"));
   
  return result;
} 
                                           
ExtensionEncoding constructTheoryExtensions(str relName, Formula relForm, Index idx, map[Atom, AtomDecl] atomsWithTheories) {
  ExtensionEncoding result = ();
  
  for (int i <- [0..size(idx)], Atom a := idx[i], a in atomsWithTheories) {
    result[i] = {constructTheoryFormula(relName, relForm, atomsWithTheories[a])};
  }
  
  return result;
}

default TheoryFormula constructTheoryFormula(str relName, Formula relForm, AtomDecl ad) { throw "No theory extension found for theory \'<ad.theory>\' for atom \'<ad.atom>\', decl = <ad>"; } 

alias TranslationResult = tuple[Formula formula, set[Formula] additionalConstraints];
                                                                                            
TranslationResult translateProblem(Problem p, Environment env) {
  set[TheoryFormula] extraTheoryConstraints = {};
  void addTheoryConstraint(set[TheoryFormula] constraints) {
    extraTheoryConstraints += constraints;
  }
  
  set[Formula] additionalConstraints = {};
  void addAdditionalConstraint(Formula constraint) {
    additionalConstraints += constraint; 
  }

  Formula baseConstraints = (\true() | and(it, r) | AlleFormula f <- p.constraints, Formula r := translateFormula(f, env, p.uni, addTheoryConstraint, addAdditionalConstraint));
  Formula extraConstraints = (\true() | and(it, r) | TheoryFormula c <- extraTheoryConstraints, Formula r := \if(c.relForm, c.theoryForm));
  
  return <\and(baseConstraints, extraConstraints), additionalConstraints>; 
}

Environment constructSingleton(str newVarName, list[Atom] vector, RelationMatrix origMatrix) = (newVarName : (vector : <\true(), origMatrix[vector].ext>));

//@memo
Formula translateFormula(empty(Expr expr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) 
  = \not(translateFormula(nonEmpty(expr), env, uni, addTheoryConstraint, addAdditionalConstraint));

//@memo
Formula translateFormula(atMostOne(Expr expr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint)   
  = \or(translateFormula(empty(expr), env, uni, addTheoryConstraint, addAdditionalConstraint), translateFormula(exactlyOne(expr), env, uni, addTheoryConstraint, addAdditionalConstraint));

//@memo
Formula translateFormula(exactlyOne(Expr expr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) 
  = (\false() | \or(it, \and(m[x].relForm, (\true() | \and(it, \not(m[y].relForm)) | Index y <- m, y != x))) | Index x <- m)    
    when RelationMatrix m := translateExpression(expr, env, uni, addTheoryConstraint, addAdditionalConstraint);
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

//@memo
Formula translateFormula(nonEmpty(Expr expr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) = (\false() | \or(it,  m[x].relForm) | Index x <- m)
  when RelationMatrix m := translateExpression(expr, env, uni, addTheoryConstraint, addAdditionalConstraint);
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

//@memo
Formula translateFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) 
  //= m == () ? \false() : (\true() | \and(it, m[x]) | Index x <- m, x.theory == relTheory())
  //when Binding lhs := translateExpression(lhsExpr, env, uni),
  //   Binding rhs := translateExpression(rhsExpr, env, uni),
  //   Binding m :=(idx:\or({\not(lhsVal), rhsVal}) | Index idx <- (lhs + rhs), idx.theory == relTheory(), Formula lhsVal := ((idx in lhs) ? lhs[idx] : \false()), Formula rhsVal := ((idx in rhs) ? rhs[idx] : \false())); 
{
  RelationMatrix lhs = translateExpression(lhsExpr, env, uni, addTheoryConstraint, addAdditionalConstraint);
  RelationMatrix rhs = translateExpression(rhsExpr, env, uni, addTheoryConstraint, addAdditionalConstraint);
  
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
     
//@memo     
Formula translateFormula(equal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint)
  = \and(translateFormula(subset(lhsExpr, rhsExpr), env, uni, addTheoryConstraint, addAdditionalConstraint), translateFormula(subset(rhsExpr, lhsExpr), env, uni, addTheoryConstraint, addAdditionalConstraint));

//@memo
Formula translateFormula(inequal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) 
  = translateFormula(negation(equal(lhsExpr, rhsExpr)), env, uni, addTheoryConstraint, addAdditionalConstraint);
  
//@memo  
Formula translateFormula(negation(AlleFormula form), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) 
  = \not(translateFormula(form, env, uni, addTheoryConstraint, addAdditionalConstraint));

//@memo  
Formula translateFormula(conjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint)
  = \and(translateFormula(lhsForm, env, uni, addTheoryConstraint, addAdditionalConstraint), translateFormula(rhsForm, env, uni, addTheoryConstraint, addAdditionalConstraint));

//@memo  
Formula translateFormula(disjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint)
  = \or(translateFormula(lhsForm, env, uni, addTheoryConstraint, addAdditionalConstraint), translateFormula(rhsForm, env, uni, addTheoryConstraint, addAdditionalConstraint));

//@memo  
Formula translateFormula(implication(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint)
  = \or(\not(translateFormula(lhsForm, env, uni, addTheoryConstraint, addAdditionalConstraint)), translateFormula(rhsForm, env, uni, addTheoryConstraint, addAdditionalConstraint));

//@memo  
Formula translateFormula(equality(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint)
  = \or(\and(translateFormula(lhsForm, env, uni, addTheoryConstraint, addAdditionalConstraint),  translateFormula(rhsForm, env, uni, addTheoryConstraint, addAdditionalConstraint)), \and(\not(translateFormula(lhsForm, env, uni, addTheoryConstraint, addAdditionalConstraint)), \not(translateFormula(rhsForm, env, uni, addTheoryConstraint, addAdditionalConstraint))));

data Formula 
  = substitutes(Environment subs)
  ; 

//@memo
Formula translateFormula(universal(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) 
{
  Formula buildOr([], Environment extendedEnvironment) = substitutes(extendedEnvironment);

  Formula buildOr([VarDeclaration hd, *VarDeclaration tl], Environment extendedEnvironment) {
    set[Formula] result = {};
    
    RelationMatrix m = translateExpression(hd.binding, env + extendedEnvironment, uni, addTheoryConstraint, addAdditionalConstraint);
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
    case substitutes(Environment subs) => translateFormula(form, env + subs, uni, addTheoryConstraint, addAdditionalConstraint)
  }
  
  return result;
}
  //= \and({\or({\not(m[x]), translateFormula(f, env + singletonConstructor.constructSingleton(hd.name, m, x.vector), uni)}) | Index x <- m, x.theory == relTheory(), AlleFormula f := (([] == t) ? form : universal(t, form))})
  //when [VarDeclaration hd, *t] := decls,
  //     Binding m := translateExpression(hd.binding, env, uni);

//@memo   
Formula translateFormula(existential(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) {
  set[Formula] clauses = {};
    
  VarDeclaration hd = decls[0];
  list[VarDeclaration] tl = (size(decls) > 1) ? decls[1..] : [];
  
  RelationMatrix m = translateExpression(hd.binding, env, uni, addTheoryConstraint, addAdditionalConstraint);
  
  for (Index x <- m, m[x].relForm != \false()) {
    AlleFormula f = tl != [] ? existential(tl, form) : form;

    Formula clause = \and(m[x].relForm, translateFormula(f, env + constructSingleton(hd.name, x, m), uni, addTheoryConstraint, addAdditionalConstraint));
    
    if (clause == \true()) { return \true(); }
    clauses += clause;
  }
  
  return \or(clauses);
}

//Formula translateFormula(existential(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni)
//  = \or({\and({m[x], translateFormula(f, env + singletonConstructor.constructSingleton(hd.name, m, x.vector), uni)}) | Index x <- m, x.theory == relTheory(), AlleFormula f := (([] == t) ? form : existential(t, form))}) 
//  when [VarDeclaration hd, *t] := decls,
//       Binding m := translateExpression(hd.binding, env, uni);

default Formula translateFormula(AlleFormula f, Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) { throw "Translation of formula \'<f>\' not supported"; }

//@memo
RelationMatrix translateExpression(variable(str name), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) = env[name];
//@memo
RelationMatrix translateExpression(transpose(Expr expr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) = transpose(m)
  when RelationMatrix m := translateExpression(expr, env, uni, addTheoryConstraint, addAdditionalConstraint); 
//@memo
RelationMatrix translateExpression(closure(Expr expr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) = transitiveClosure(m, uni, addTheoryConstraint, addAdditionalConstraint)
  when RelationMatrix m := translateExpression(expr, env, uni, addTheoryConstraint, addAdditionalConstraint);
//@memo     
RelationMatrix translateExpression(reflexClosure(Expr expr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) = reflexiveTransitiveClosure(m, uni, addTheoryConstraint, addAdditionalConstraint)
  when RelationMatrix m := translateExpression(expr, env, uni, addTheoryConstraint, addAdditionalConstraint);
//@memo    
RelationMatrix translateExpression(union(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) = disjunction(lhs,rhs)  
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint, addAdditionalConstraint),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint, addAdditionalConstraint);
//@memo  
RelationMatrix translateExpression(intersection(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) = conjunction(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint, addAdditionalConstraint),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint, addAdditionalConstraint);
//@memo
RelationMatrix translateExpression(difference(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) = difference(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint, addAdditionalConstraint),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint, addAdditionalConstraint);

//@memo
RelationMatrix translateExpression(\join(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) = \join(lhs, rhs, addTheoryConstraint) 
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint, addAdditionalConstraint), 
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint, addAdditionalConstraint);

RelationMatrix translateExpression(accessorJoin(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) = translateExpression(\join(rhsExpr, lhsExpr), env, uni, addTheoryConstraint, addAdditionalConstraint);

//@memo    
RelationMatrix translateExpression(product(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) = product(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint, addAdditionalConstraint), 
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint, addAdditionalConstraint);

//@memo
RelationMatrix translateExpression(ifThenElse(AlleFormula caseForm, Expr thenExpr, Expr elseExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) {
  Formula \case = translateFormula(caseForm, env, uni, addTheoryConstraint, addAdditionalConstraint);
  RelationMatrix then = translateExpression(thenExpr, env, uni, addTheoryConstraint, addAdditionalConstraint);
  RelationMatrix \else = translateExpression(elseExpr, env, uni, addTheoryConstraint, addAdditionalConstraint);

  if (\case == \true()) {
    return then;
  } else if (\case == \false()) {
    return \else;
  } 
  
  int arityThen = arity(then);
  int arityElse = arity(\else);
  
  if (arityThen != arityElse) {
    throw "Then and Else expressions must be of same arity";
  }
  
  RelationMatrix result = ();
  for (Index idx <- (then + \else)) {
    Formula thenVal = ((idx in then) ? then[idx].relForm : \false());
    Formula elseVal = ((idx in \else) ? \else[idx].relForm : \false()); 
    ExtensionEncoding thenExt = ((idx in then) ? then[idx].ext : ());
    ExtensionEncoding elseExt = ((idx in \else) ? \else[idx].ext : ());
     
    result[idx] = <ite(\case, thenVal, elseVal), merge(thenExt, elseExt)>;
  }
  
  return result;
}

//   = (idx:<ite(translatedCase, thenRm[idx].relForm, elseRm[idx].relForm), (t : {\or(\not(translatedCase), thenTe) | Formula thenTe <- thenRm[idx].ext[t]} + {\or(translatedCase, elseTe) | Formula elseTe <- elseRm[idx].ext[t]} | Theory t <- thenRm[idx].ext)> | Index idx <- thenRm)
//  when RelationMatrix thenRm := translateExpression(thenExpr, env, uni),
//       RelationMatrix elseRm := translateExpression(elseExpr, env, uni),
//       Formula translatedCase := translateFormula(caseForm, env, uni);

//@memo     
RelationMatrix translateExpression(comprehension(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) {
  RelationMatrix calculate(Index currentIdx, [], Environment extendedEnv, Formula partialForm, ExtensionEncoding extension) =
    (currentIdx : <\and(partialForm, translateFormula(form, extendedEnv, uni, addTheoryConstraint, addAdditionalConstraint)), extension>);
  
  RelationMatrix calculate(Index currentIdx, [VarDeclaration hd, *VarDeclaration tl], Environment extendedEnv, Formula partialForm, ExtensionEncoding partialExtensions) {
    RelationMatrix result = ();
    
    RelationMatrix decl = translateExpression(hd.binding, extendedEnv, uni, addTheoryConstraint, addAdditionalConstraint);
    if (arity(decl) > 1) { throw "Higher order comprehensions are not allowed"; }
    
    for (Index idx <- decl) {
      result += calculate(currentIdx + idx, tl, extendedEnv + constructSingleton(hd.name, idx, decl), \and(partialForm, decl[idx].relForm), productExt(size(currentIdx), partialExtensions, decl[idx].ext));
    } 
    
    return result;
  }
  
  return calculate([], decls, env, \true(), ());
}

default RelationMatrix translateExpression(Expr expr, Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) { throw "Translation of expression \'<expr>\' not supported"; }

//default bool contains(TheoryExtension ext, str varName, Theory t) = false;
