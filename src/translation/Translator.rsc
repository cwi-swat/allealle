module translation::Translator

import logic::Propositional;
import translation::AST;
import translation::Binder; 
import translation::Unparser;

import logic::CBCFactory;

import IO; 
import List;

import util::Maybe;
import util::Benchmark;

alias AdditionalConstraintFunctions = tuple[void (Formula) addAttributeConstraint, void (Command) addAdditionalCommand, void (Formula) addIntermediateVar, Id () freshIntermediateId]; 
  
alias FormulaCacheKey = tuple[AlleFormula form, Environment env];
alias ExprCacheKey = tuple[AlleExpr expr, Environment env];

alias FormulaCache = map[FormulaCacheKey, Formula]; 
alias ExprCache = map[ExprCacheKey, RelationMatrix];

data Cache = cache(Maybe[Formula] (FormulaCacheKey) formulaLookup, void (FormulaCacheKey, Formula) storeFormula, Maybe[RelationMatrix] (ExprCacheKey) exprLookup, void (ExprCacheKey, RelationMatrix) storeExpr);

alias TranslationResult = tuple[Formula relationalFormula, Formula attributeFormula, set[Formula] intermediateVars, list[Command] additionalCommands];

Environment createInitialEnvironment(Problem p) {
  map[str, RelationMatrix] relations = (r.name:createRelationMatrix(r) | Relation r <- p.relations);
  map[Index, map[str, Formula]] attributes = (() | createAttributeLookup(r, it) | r:relationWithAttributes(str name, int arityOfIds, list[AttributeHeader] headers, RelationalBound bounds) <- p.relations); 
   
  return <relations, attributes>;
}   
                                                                                                                                                    
RelationMatrix createRelationMatrix(Relation r) {
  str idxToStr(Index idx) = intercalate("_", idx);
  
  tuple[list[Index] lb, list[Index] ub] bounds = getBounds(r.arityOfIds, r.bounds);
  
  RelationMatrix relResult = (); 
    
  for (Index idx <- bounds.lb) {
    relResult += (idx : relOnly(\true()));
  }

  for (Index idx <- bounds.ub, idx notin bounds.lb) {
    relResult += (idx : relOnly(var("<r.name>_<idxToStr(idx)>")));
  }

  return relResult;
} 

tuple[list[Index], list[Index]] getBounds(int arity, exact(list[Tuple] tuples)) = <b,b> when list[Index] b := getIndices(arity, tuples);
tuple[list[Index], list[Index]] getBounds(int arity, atMost(list[Tuple] upper)) = <[], ub> when list[Index] ub := getIndices(arity, upper);
tuple[list[Index], list[Index]] getBounds(int arity, atLeastAtMost(list[Tuple] lower, list[Tuple] upper)) = <lb,ub> when list[Index] lb := getIndices(arity, lower), list[Index] ub := getIndices(arity, upper);
      
private list[Index] getIndices(int arity, list[Tuple] tuples) {
  list[Index] indices = [];
  for (Tuple t <- tuples) {
     Index idx = [id | id(Id id) <- t.values];
     
     if (size(idx) != arity) {
      throw "Arity definition of id field and nr of ids in tuples do not match";
     }
     
     indices += [idx];
  }
  
  return indices;
}

map[Index, map[str, Formula]] createAttributeLookup(relationWithAttributes(str _, int arityOfIds, list[AttributeHeader] headers, RelationalBound bounds), map[Index, map[str, Formula]] currentLookup) {
  map[Index, map[str, Formula]] partial = createPartialAttributeLookup(arityOfIds, headers, bounds);
  
  for (Index idx <- partial) {
    if (idx in currentLookup) {
      currentLookup[idx] += partial[idx];
    } else {
      currentLookup[idx] = partial[idx];
    }
  }     
  
  return currentLookup;
} 

map[Index, map[str, Formula]] createPartialAttributeLookup(int arityOfIds, list[AttributeHeader] headers, exact(list[Tuple] tuples)) = createPartialAttributeLookup(arityOfIds, headers, tuples);
map[Index, map[str, Formula]] createPartialAttributeLookup(int arityOfIds, list[AttributeHeader] headers, atMost(list[Tuple] upper)) = createPartialAttributeLookup(arityOfIds, headers, upper);
map[Index, map[str, Formula]] createPartialAttributeLookup(int arityOfIds, list[AttributeHeader] headers, atLeastAtMost(list[Tuple] _, list[Tuple] upper)) = createPartialAttributeLookup(arityOfIds, headers, upper);

private map[Index, map[str, Formula]] createPartialAttributeLookup(int arityOfIds, list[AttributeHeader] headers, list[Tuple] tuples) {
  map[Index, map[str, Formula]] result = ();
  
  for (Tuple t <- tuples) {
    Index idx = [id | id(Id id) <- t.values];
    if (arityOfIds + size(headers) != size(t.values)) {
      throw "Total arity of relation and size of the defined tuples differ";
    }

    map[str, Formula] attributes = ();
        
    for (int i <- [0..size(headers)], AttributeHeader h := headers[i], Value v := t.values[arityOfIds + i]) {
      attributes[h.name] = createAttribute(idx, h.name, h.dom, v);  
    }
    
    result[idx] = attributes;  
  }
  
  return result;
}      
                                           
default Formula createAttribute(Index idx, str name, Domain d, Value v) { throw "No attribute creator found for domain \'<d>\' with value \'<v>\'"; } 
                                                                                            
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
  
  set[Formula] intermediateVars = {};
  void addIntermediateVar(Formula val) {
    intermediateVars += val;
  }
   
  int tmpNr = 0;  
  Id freshIntermediateId() {
    tmpNr += 1;
    return "_tmp_<tmpNr>";
  }
   
  Formula relForm = and({r | AlleFormula f <- p.constraints, bprint("\nTranslating \'<unparse(f)>\' ..."), <Formula r, int time> := bm(f, env, <addAttributeConstraint, addAdditionalCommand, addIntermediateVar, freshIntermediateId>, cache(formulaLookup, storeFormula, exprLookup, storeExpr)), bprint("in <time / 1000000> ms.")});
  Formula attForm = and(attributeConstraints);
  
  return <relForm, attForm, intermediateVars, additionalCommands>; 
}

bool bprint(str line) { 
  print(line);
  return true;
}

private tuple[Formula, int] bm(AlleFormula f, Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  int startTime = cpuTime();
  Formula result = translateCachedFormula(f, env, acf, cache);
  return <result, cpuTime() - startTime>;
}

map[str, RelationMatrix] constructSingleton(str newVarName, Index idx) = (newVarName : (idx : relOnly(\true())));

Formula translateCachedFormula(AlleFormula f, Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  if (just(Formula r) := cache.formulaLookup(<f,env>)) {
    return r;
  }
  
  Formula r = translateFormula(f,env,acf,cache);
  cache.storeFormula(<f,env>, r);
  
  return r;
} 

Formula translateFormula(empty(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf, Cache cache) 
  = \not(translateCachedFormula(nonEmpty(expr), env, acf, cache));

Formula translateFormula(atMostOne(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf, Cache cache) 
  = \or(translateCachedFormula(empty(expr), env, acf, cache), translateCachedFormula(exactlyOne(expr), env, acf, cache));

Formula translateFormula(exactlyOne(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix m = translateCachedExpression(expr, env, acf, cache);
  
  set[Formula] outer = {};
  
  for (Index x <- m) {
    set[Formula] inner = {};    

    if (m[x].relForm == \false()) {
      inner += \false();
    } else {

      for (Index y <- m, y != x, m[y].relForm != \false()) {
        inner += not(m[y].relForm);
      }
    
      Formula innerAnd = \and({m[x].relForm, *inner});
      if (innerAnd == \true()) {
        return \true();
      }
    
      outer += innerAnd;
    }
  }
  
  return \or(outer);
}
  //= (\false() | \or(it, \and(m[x].relForm, (\true() | \and(it, \not(m[y].relForm)) | Index y <- m, y != x))) | Index x <- m)    
  //  when RelationMatrix m := translateCachedExpression(expr, env, acf, cache);

Formula translateFormula(nonEmpty(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix m = translateCachedExpression(expr, env, acf, cache);
  
  set[Formula] clauses = {};
  
  for (Index idx <- m) {
    if (m[idx].relForm == \true()) {
      return \true();
    }
    
    clauses += m[idx].relForm;
  } 
  
  return \or(clauses);
}

Formula translateFormula(subset(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix lhs = translateCachedExpression(lhsExpr, env, acf, cache);
  RelationMatrix rhs = translateCachedExpression(rhsExpr, env, acf, cache);
  
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
     
Formula translateFormula(equal(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf, Cache cache)
  = \and(translateCachedFormula(subset(lhsExpr, rhsExpr), env, acf, cache), translateCachedFormula(subset(rhsExpr, lhsExpr), env, acf, cache));

Formula translateFormula(inequal(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf, Cache cache) 
  = translateCachedFormula(negation(equal(lhsExpr, rhsExpr)), env, acf, cache);
  
Formula translateFormula(negation(AlleFormula form), Environment env, AdditionalConstraintFunctions acf, Cache cache) 
  = \not(translateCachedFormula(form, env, acf, cache));

Formula translateFormula(conjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  Formula l = translateCachedFormula(lhsForm, env, acf, cache);
  if (l == \false()) {
    return \false();
  }
  
  return \and(l, translateCachedFormula(rhsForm, env, acf, cache));
}

Formula translateFormula(disjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  Formula l = translateCachedFormula(lhsForm, env, acf, cache);
  if (l == \true()) {
     return \true();
  }
  
  return \or(l, translateCachedFormula(rhsForm, env, acf, cache));
}

Formula translateFormula(implication(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  Formula l = translateCachedFormula(lhsForm, env, acf, cache);
  if (l == \false()) {
    return \true();
  }
  
  return \or(\not(l), translateCachedFormula(rhsForm, env, acf, cache));
}

Formula translateFormula(equality(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  Formula l = translateCachedFormula(lhsForm, env, acf, cache);
  Formula r = translateCachedFormula(rhsForm, env, acf, cache);
  
  return \or(\and(l,r), \and(\not(l), \not(r)));
}

private Environment extEnv(Environment orig, map[str, RelationMatrix] newRelations) = <orig.relations + newRelations, orig.attributes>; 

Formula translateFormula(let(list[VarDeclaration] decls, AlleFormula form), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  Environment extendedEnv = env;
  
  for (VarDeclaration decl <- decls) {
    RelationMatrix b = translateCachedExpression(decl.binding, extendedEnv, acf, cache);
    extendedEnv = extEnv(extendedEnv, (decl.name : b));
  }
  
  return translateCachedFormula(form, extendedEnv, acf, cache);
}

data Formula 
  = substitutes(Environment subs)
  ; 

Formula translateFormula(universal(list[VarDeclaration] decls, AlleFormula form), Environment env, AdditionalConstraintFunctions acf, Cache cache) 
  = translateQuantification(Formula (Formula l, Formula r) { return \or(\not(l), r); }, Formula (set[Formula] clauses) { return  \and(clauses); }, decls, form, env, acf, cache);

Formula translateFormula(existential(list[VarDeclaration] decls, AlleFormula form), Environment env, AdditionalConstraintFunctions acf, Cache cache) 
  = translateQuantification(Formula (Formula l, Formula r) { return \and(l,r); }, Formula (set[Formula] clauses) { return \or(clauses); }, decls, form, env, acf, cache);

private Formula translateQuantification(Formula (Formula, Formula) innerOpper, Formula (set[Formula]) outerOpper, list[VarDeclaration] decls, AlleFormula form, Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  
  Formula buildForm([], map[str,RelationMatrix] extraBindings) = translateCachedFormula(form, extEnv(env, extraBindings), acf, cache); //substitutes(extEnv(env, extraBindings));

  Formula buildForm([VarDeclaration hd, *VarDeclaration tl], map[str,RelationMatrix] extraBindings) {
    set[Formula] result = {};
    
    RelationMatrix m = translateCachedExpression(hd.binding, extEnv(env, extraBindings), acf, cache);

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
  
  //result = visit(result) {
  //  case substitutes(Environment subs) => translateCachedFormula(form, subs, acf, cache)
  //}
  
  return result;
}

default Formula translateFormula(AlleFormula f, Environment env, AdditionalConstraintFunctions acf, Cache cache) { throw "Translation of formula \'<f>\' not supported"; }

RelationMatrix translateCachedExpression(AlleExpr e, Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  if (just(RelationMatrix r) := cache.exprLookup(<e,env>)) {
    return r;
  }
  
  RelationMatrix r = translateExpression(e, env, acf, cache);
  cache.storeExpr(<e,env>, r);
  
  return r;  
}

RelationMatrix translateExpression(variable(str name), Environment env, AdditionalConstraintFunctions acf, Cache cache) = env.relations[name];

RelationMatrix translateExpression(attributeLookup(AlleExpr e, str name), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix m = translateCachedExpression(e, env, acf, cache);
  
  if (m == ()) {
    return ();
  }
  
  for (Index idx <- m) {
    if (idx notin env.attributes || name notin env.attributes[idx]) {
      throw "Attribute \'<name>\' not defined on \'<idx>\' ";
    }
    
    m[idx] = relAndAtt(m[idx].relForm, env.attributes[idx][name]);
  }
  
  return m;   
}

RelationMatrix translateExpression(transpose(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf, Cache cache) = transpose(m)
  when RelationMatrix m := translateCachedExpression(expr, env, acf, cache); 

RelationMatrix translateExpression(closure(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf, Cache cache) = transitiveClosure(m)
  when RelationMatrix m := translateCachedExpression(expr, env, acf, cache);

RelationMatrix translateExpression(reflexClosure(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf, Cache cache) = reflexiveTransitiveClosure(m, env)
  when RelationMatrix m := translateCachedExpression(expr, env, acf, cache);

RelationMatrix translateExpression(union(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf, Cache cache) = or(lhs,rhs)  
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, acf, cache),
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, acf, cache);

RelationMatrix translateExpression(intersection(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf, Cache cache) = and(lhs, rhs)
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, acf, cache),
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, acf, cache);

RelationMatrix translateExpression(difference(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf, Cache cache) = difference(lhs, rhs)
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, acf, cache),
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, acf, cache);

RelationMatrix translateExpression(\join(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix lhs = translateCachedExpression(lhsExpr, env, acf, cache); 
  RelationMatrix rhs = translateCachedExpression(rhsExpr, env, acf, cache);
  
  return dotJoin(lhs, rhs); 
}

RelationMatrix translateExpression(accessorJoin(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf, Cache cache) = translateCachedExpression(\join(rhsExpr, lhsExpr), env, acf, cache);

RelationMatrix translateExpression(product(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf, Cache cache) = product(lhs, rhs)
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, acf, cache), 
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, acf, cache);

RelationMatrix translateExpression(ifThenElse(AlleFormula caseForm, AlleExpr thenExpr, AlleExpr elseExpr), Environment env, AdditionalConstraintFunctions acf, Cache cache) = ite(\case, then, \else)
  when Formula \case := translateCachedFormula(caseForm, env, acf, cache),
       RelationMatrix then := translateCachedExpression(thenExpr, env, acf, cache),
       RelationMatrix \else := translateCachedExpression(elseExpr, env, acf, cache);

RelationMatrix translateExpression(comprehension(list[VarDeclaration] decls, AlleFormula form), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix calculate(Index idx, [], Environment extendedEnv, Formula partialRelForm) {
    if (partialRelForm == \false()) {
      return (idx:relOnly(\false()));
    }
    
    return (idx : relOnly(and(partialRelForm, translateCachedFormula(form, extendedEnv, acf, cache))));
  }
  
  RelationMatrix calculate(Index currentIdx, [VarDeclaration hd, *VarDeclaration tl], Environment extendedEnv, Formula partialRelForm) {
    RelationMatrix relResult = ();
    
    RelationMatrix decl = translateCachedExpression(hd.binding, extendedEnv, acf, cache);
    if (arity(decl) > 1) { throw "Higher order comprehensions are not allowed"; }
    
    for (Index idx <- decl) {
      relResult += calculate(currentIdx + idx, tl, extEnv(extendedEnv, constructSingleton(hd.name, idx)), \and(partialRelForm, decl[idx].relForm));
    } 
    
    return relResult;
  }
  
  return calculate([], decls, env, \true());
}

default RelationMatrix translateExpression(AlleExpr expr, Environment env, AdditionalConstraintFunctions acf, Cache cache) { throw "Translation of expression \'<expr>\' not supported"; }
