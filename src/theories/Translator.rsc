module theories::Translator

import logic::Propositional;
import theories::AST;
import theories::Binder; 
import theories::Unparser;

import IO;
import List;

import util::Maybe;
import util::Benchmark;

alias AdditionalConstraintFunctions = tuple[void (Formula) addAttributeConstraint, void (Command) addAdditionalCommand, void (AtomDecl) addAtomToUniverse, Atom () freshAtom]; 

alias FormulaCacheKey = tuple[AlleFormula form, Environment env];
alias ExprCacheKey = tuple[Expr expr, Environment env];

alias FormulaCache = map[FormulaCacheKey, Formula];
alias ExprCache = map[ExprCacheKey, RelationMatrix];

data Cache = cache(Maybe[Formula] (FormulaCacheKey) formulaLookup, void (FormulaCacheKey, Formula) storeFormula, Maybe[RelationMatrix] (ExprCacheKey) exprLookup, void (ExprCacheKey, RelationMatrix) storeExpr);

//data Cache = cache(FormulaCache formulaCache, ExprCache exprCache);

Environment createInitialEnvironment(Problem p) {
  map[str, RelationMatrix] relations = (rb.relName:createRelationalMapping(rb) | RelationalBound rb <- p.bounds);
  map[Atom, map[str, Formula]] attributes = (a : createAttributeMap(ad) | ad:atomWithAttributes(Atom a, list[Attribute] attributes) <- p.uni.atoms); 
  
  return <relations, attributes>;
} 
                                                                                                                                                    
RelationMatrix createRelationalMapping(relationalBound(str relName, int arity, list[Tuple] lb, list[Tuple] ub)) {
  str idxToStr(list[Atom] idx) = intercalate("_", idx);
  
  RelationMatrix relResult = ();
  
  for (\tuple(list[Atom] idx) <- lb) {
    relResult += (idx : relOnly(\true()));
  }

  for (\tuple(list[Atom] idx) <- ub, idx notin relResult) {
    relResult += (idx : relOnly(var("<relName>_<idxToStr(idx)>")));
  }

  return relResult;
} 
                                           
map[str, Formula] createAttributeMap(AtomDecl ad) = (at.name : constructAttribute(ad.atom, at) | Attribute at <- ad.attributes);  

default Formula constructAttribute(Atom a, Attribute attr) { throw "No attribute builder found for theory \'<attr.theory>\' for atom \'<a>\'"; } 

alias TranslationResult = tuple[Formula relationalFormula, Formula attributeFormula, set[AtomDecl] newAtoms, list[Command] additionalCommands];
                                                                                            
TranslationResult translateProblem(Problem p, Environment env) {
  FormulaCache formCache = ();
  ExprCache exprCache = ();
  
  Maybe[Formula] formulaLookup(FormulaCacheKey key) = just(formCache[key]) when key in formCache;
  default Maybe[Formula] formulaLookup(FormulaCacheKey key) = nothing();
  void storeFormula(FormulaCacheKey key, Formula f) { formCache[key] = f; }
  
  Maybe[RelationMatrix] exprLookup(ExprCacheKey key) = just(exprCache[key]) when key in exprCache;
  default Maybe[RelationMatrix] exprLookup(ExprCacheKey key) = nothing();
  void storeExpr(ExprCacheKey key, RelationMatrix rm) { exprCache[key] = rm; }
  
  set[Formula] attributeConstraints = {};
  
  void addAttributeConstraint(Formula constraint) {
    attributeConstraints += constraint;
  }
  
  list[Command] additionalCommands = [];
  void addAdditionalCommand(Command command) {
    additionalCommands += command;  
  }
  
  set[AtomDecl] newAtoms = {};
  void addAtomToUniverse(AtomDecl ad) {
    newAtoms += ad;
  }
  
  int resultNr = 0;
  Atom freshAtom() {
     resultNr += 1;
     return "_tmp<resultNr>";
  }
  
  Formula relForm = and({r | AlleFormula f <- p.constraints, bprint("\nTranslating \'<unparse(f)>\' ..."), <Formula r, int time> := bm(f, env, p.uni, <addAttributeConstraint, addAdditionalCommand, addAtomToUniverse, freshAtom>, cache(formulaLookup, storeFormula, exprLookup, storeExpr)), bprint("in <time / 1000000> ms.")});
  Formula attForm = and(attributeConstraints);
  
  return <relForm, attForm, newAtoms, additionalCommands>; 
}

bool bprint(str line) { 
  print(line);
  return true;
}

private tuple[Formula, int] bm(AlleFormula f, Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  int startTime = userTime();
  Formula result = translateCachedFormula(f, env, uni, acf, cache);
  return <result, userTime() - startTime>;
}

map[str, RelationMatrix] constructSingleton(str newVarName, list[Atom] vector) = (newVarName : (vector : relOnly(\true())));

Formula translateCachedFormula(AlleFormula f, Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  if (just(Formula r) := cache.formulaLookup(<f,env>)) {
    return r;
  }
  
  Formula r = translateFormula(f,env,uni,acf,cache);
  cache.storeFormula(<f,env>, r);
  
  return r;
} 

Formula translateFormula(empty(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) 
  = \not(translateCachedFormula(nonEmpty(expr), env, uni, acf, cache));

Formula translateFormula(atMostOne(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) 
  = \or(translateCachedFormula(empty(expr), env, uni, acf, cache), translateCachedFormula(exactlyOne(expr), env, uni, acf, cache));

Formula translateFormula(exactlyOne(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) 
  = (\false() | \or(it, \and(m[x].relForm, (\true() | \and(it, \not(m[y].relForm)) | Index y <- m, y != x))) | Index x <- m)    
    when RelationMatrix m := translateCachedExpression(expr, env, uni, acf, cache);

Formula translateFormula(nonEmpty(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix m = translateCachedExpression(expr, env, uni, acf, cache);
  
  Formula result = \false();
  
  for (Index idx <- m) {
    if (m[idx].relForm == \true()) {
      return \true();
    }
    
    result = \or(result, m[idx].relForm);
  } 
  
  return result;
}

Formula translateFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix lhs = translateCachedExpression(lhsExpr, env, uni, acf, cache);
  RelationMatrix rhs = translateCachedExpression(rhsExpr, env, uni, acf, cache);
  
  RelationMatrix m = ();
  for (Index idx <- (lhs + rhs)) {
    Formula lhsVal = (idx in lhs) ? lhs[idx].relForm : \false();
    Formula rhsVal = (idx in rhs) ? rhs[idx].relForm : \false();
 
    m[idx] = relOnly(\or(\not(lhsVal), rhsVal));
    if (m[idx].relForm == \false()) {
      return \false();
    }
  } 

  if (m == ()) {
    return \false();
  }

  Formula result = \true();
  for (Index idx <- m) {  
    result = \and(result, m[idx].relForm);
  }
  
  return result;
}
     
Formula translateFormula(equal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache)
  = \and(translateCachedFormula(subset(lhsExpr, rhsExpr), env, uni, acf, cache), translateCachedFormula(subset(rhsExpr, lhsExpr), env, uni, acf, cache));

Formula translateFormula(inequal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) 
  = translateCachedFormula(negation(equal(lhsExpr, rhsExpr)), env, uni, acf, cache);
  
Formula translateFormula(negation(AlleFormula form), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) 
  = \not(translateCachedFormula(form, env, uni, acf, cache));

Formula translateFormula(conjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  Formula l = translateCachedFormula(lhsForm, env, uni, acf, cache);
  if (l == \false()) {
    return \false();
  }
  
  return \and(l, translateCachedFormula(rhsForm, env, uni, acf, cache));
}

Formula translateFormula(disjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  Formula l = translateCachedFormula(lhsForm, env, uni, acf, cache);
  if (l == \true()) {
     return \true();
  }
  
  return \or(l, translateCachedFormula(rhsForm, env, uni, acf, cache));
}

Formula translateFormula(implication(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  Formula l = translateCachedFormula(lhsForm, env, uni, acf, cache);
  if (l == \false()) {
    return \true();
  }
  
  return \or(\not(l), translateCachedFormula(rhsForm, env, uni, acf, cache));
}

Formula translateFormula(equality(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  Formula l = translateCachedFormula(lhsForm, env, uni, acf, cache);
  Formula r = translateCachedFormula(rhsForm, env, uni, acf, cache);
  
  return \or(\and(l,r), \and(\not(l), \not(r)));
}

private Environment extEnv(Environment orig, map[str, RelationMatrix] newRelations) = <orig.relations + newRelations, orig.attributes>; 

Formula translateFormula(let(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  Environment extendedEnv = env;
  
  for (VarDeclaration decl <- decls) {
    RelationMatrix b = translateCachedExpression(decl.binding, extendedEnv, uni, acf, cache);
    extendedEnv = extEnv(extendedEnv, (decl.name : b));
  }
  
  return translateCachedFormula(form, extendedEnv, uni, acf, cache);
}

data Formula 
  = substitutes(Environment subs)
  ; 

Formula translateFormula(universal(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) 
  = translateQuantification(Formula (Formula l, Formula r) { return \or(\not(l), r); }, Formula (set[Formula] clauses) { return  \and(clauses); }, decls, form, env, uni, acf, cache);
  
//{
//  Formula buildOr([], map[str,RelationMatrix] extraBindings) = substitutes(extEnv(env, extraBindings));
//
//  Formula buildOr([VarDeclaration hd, *VarDeclaration tl], map[str,RelationMatrix] extraBindings) {
//    set[Formula] result = {};
//    
//    RelationMatrix m = translateExpression(hd.binding, extEnv(env, extraBindings), uni, acf);
//
//    for (Index idx <- m) {
//      Formula clause = buildOr(tl, extraBindings + constructSingleton(hd.name, idx));
//    
//      if (clause == \false() && m[idx].relForm == \true()) {
//        return \false();
//      }
//      
//      result += \or(\not(m[idx].relForm), clause);   
//    }    
//    
//    return \and(result);
//  }
//  
//  Formula result = buildOr(decls, ());
//  
//  result = visit(result) {
//    case substitutes(Environment subs) => translateFormula(form, subs, uni, acf)
//  }
//  
//  return result;
//}

Formula translateFormula(existential(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) 
  = translateQuantification(Formula (Formula l, Formula r) { return \and(l,r); }, Formula (set[Formula] clauses) { return \or(clauses); }, decls, form, env, uni, acf, cache);
//{
//  set[Formula] clauses = {};
//    
//  VarDeclaration hd = decls[0];
//  list[VarDeclaration] tl = (size(decls) > 1) ? decls[1..] : [];
//  
//  RelationMatrix m = translateExpression(hd.binding, env, uni, acf);
//  
//  for (Index x <- m, m[x].relForm != \false()) {
//    AlleFormula f = tl != [] ? existential(tl, form) : form;
//
//    Formula clause = \and(m[x].relForm, translateFormula(f, extEnv(env, constructSingleton(hd.name, x)), uni, acf));
//    
//    if (clause == \true()) { return \true(); }
//    clauses += clause;
//  }
//  
//  return \or(clauses);
//}

private Formula translateQuantification(Formula (Formula, Formula) innerOpper, Formula (set[Formula]) outerOpper, list[VarDeclaration] decls, AlleFormula form, Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  
  Formula buildForm([], map[str,RelationMatrix] extraBindings) = substitutes(extEnv(env, extraBindings));

  Formula buildForm([VarDeclaration hd, *VarDeclaration tl], map[str,RelationMatrix] extraBindings) {
    set[Formula] result = {};
    
    RelationMatrix m = translateCachedExpression(hd.binding, extEnv(env, extraBindings), uni, acf, cache);

    for (Index idx <- m) {
      Formula clause = buildForm(tl, extraBindings + constructSingleton(hd.name, idx));
    
      if (clause == \false() && m[idx].relForm == \true()) {
        return \false();
      }
      
      result += innerOpper(m[idx].relForm, clause);   
    }    
    
    return outerOpper(result);
  }
  
  Formula result = buildForm(decls, ());
  
  result = visit(result) {
    case substitutes(Environment subs) => translateCachedFormula(form, subs, uni, acf, cache)
  }
  
  return result;
}

default Formula translateFormula(AlleFormula f, Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) { throw "Translation of formula \'<f>\' not supported"; }

RelationMatrix translateCachedExpression(Expr e, Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  if (just(RelationMatrix r) := cache.exprLookup(<e,env>)) {
    return r;
  }
  
  RelationMatrix r = translateExpression(e, env, uni, acf, cache);
  cache.storeExpr(<e,env>, r);
  
  return r;  
}

RelationMatrix translateExpression(variable(str name), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = env.relations[name];

RelationMatrix translateExpression(attributeLookup(Expr e, str name), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix m = translateCachedExpression(e, env, uni, acf, cache);
  if (m == ()) {
    return ();
  }
  
  if (arity(m) != 1) {
    throw "Can only lookup attributes on an unary relation";
  }
  
  for (idx:[Atom a] <- m) {
    if (a notin env.attributes || name notin env.attributes[a]) {
      throw "Attribute \'<name>\' not defined on \'<a>\' ";
    }
    
    m[idx] = relAndAtt(m[idx].relForm, env.attributes[a][name]);
  }
  
  return m;   
}

RelationMatrix translateExpression(transpose(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = transpose(m)
  when RelationMatrix m := translateCachedExpression(expr, env, uni, acf, cache); 

RelationMatrix translateExpression(closure(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = transitiveClosure(m)
  when RelationMatrix m := translateCachedExpression(expr, env, uni, acf, cache);

RelationMatrix translateExpression(reflexClosure(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = reflexiveTransitiveClosure(m, uni)
  when RelationMatrix m := translateCachedExpression(expr, env, uni, acf, cache);

RelationMatrix translateExpression(union(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = or(lhs,rhs)  
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, uni, acf, cache),
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, uni, acf, cache);

RelationMatrix translateExpression(intersection(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = and(lhs, rhs)
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, uni, acf, cache),
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, uni, acf, cache);

RelationMatrix translateExpression(difference(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = difference(lhs, rhs)
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, uni, acf, cache),
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, uni, acf, cache);

RelationMatrix translateExpression(\join(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = \join(lhs, rhs) 
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, uni, acf, cache), 
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, uni, acf, cache);

RelationMatrix translateExpression(accessorJoin(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = translateCachedExpression(\join(rhsExpr, lhsExpr), env, uni, acf, cache);

RelationMatrix translateExpression(product(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = product(lhs, rhs)
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, uni, acf, cache), 
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, uni, acf, cache);

RelationMatrix translateExpression(ifThenElse(AlleFormula caseForm, Expr thenExpr, Expr elseExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = ite(\case, then, \else)
  when Formula \case := translateCachedFormula(caseForm, env, uni, acf, cache),
       RelationMatrix then := translateCachedExpression(thenExpr, env, uni, acf, cache),
       RelationMatrix \else := translateCachedExpression(elseExpr, env, uni, acf, cache);

RelationMatrix translateExpression(comprehension(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix calculate(Index idx, [], Environment extendedEnv, Formula partialRelForm) {
    if (partialRelForm == \false()) {
      return (idx:relOnly(\false()));
    }
    
    return (idx : relOnly(and(partialRelForm, translateCachedFormula(form, extendedEnv, uni, acf, cache))));
  }
  
  RelationMatrix calculate(Index currentIdx, [VarDeclaration hd, *VarDeclaration tl], Environment extendedEnv, Formula partialRelForm) {
    RelationMatrix relResult = ();
    
    RelationMatrix decl = translateCachedExpression(hd.binding, extendedEnv, uni, acf, cache);
    if (arity(decl) > 1) { throw "Higher order comprehensions are not allowed"; }
    
    for (Index idx <- decl) {
      relResult += calculate(currentIdx + idx, tl, extEnv(extendedEnv, constructSingleton(hd.name, idx)), \and(partialRelForm, decl[idx].relForm));
    } 
    
    return relResult;
  }
  
  return calculate([], decls, env, \true());
}

default RelationMatrix translateExpression(Expr expr, Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) { throw "Translation of expression \'<expr>\' not supported"; }
