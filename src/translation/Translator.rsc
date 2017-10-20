module translation::Translator

import logic::Propositional;
import translation::AST;
import translation::Binder; 
import translation::Dimensions;
import translation::Unparser;

//import logic::CBCFactory;

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
  list[Id] universe = extractUniverse(p);
  
  map[str, RelationMatrix] relations = (r.name:createRelationMatrix(r, universe) | Relation r <- p.relations);
  map[list[Id], map[str, Formula]] attributes = (() | createAttributeLookup(r, it) | r:relationWithAttributes(str name, int arityOfIds, list[AttributeHeader] headers, RelationalBound bounds) <- p.relations); 
   
  return <relations, attributes, universe>;
} 

list[Id] extractUniverse(Problem p) {
  list[Tuple] getTuples(exact(list[Tuple] tuples)) = tuples;
  list[Tuple] getTuples(atMost(list[Tuple] upper)) = upper;
  list[Tuple] getTuples(atLeastAtMost(_, list[Tuple] upper)) = upper;
  
  return dup([id | Relation r <- p.relations, Tuple t <- getTuples(r.bounds), id(Id id) <- t.values]);   
}  
                                                                                                                                                    
RelationMatrix createRelationMatrix(Relation r, list[Id] universe) { 
  @memo
  str idxToStr(list[Id] idx) = intercalate("_", idx);
  
  tuple[list[list[Id]] lb, list[list[Id]] ub] bounds = getBounds(r.arityOfIds, r.bounds);
  
  map[Index,Cell] relResult = (); 
    
  for (list[Id] idx <- bounds.lb) {
    relResult += (getIntIndex(idx, universe) : relOnly(\true()));
  }

  for (list[Id] idx <- bounds.ub, idx notin bounds.lb) {
    relResult += (getIntIndex(idx, universe) : relOnly(var("<r.name>_<idxToStr(idx)>")));
  }
 
  return <square(r.arityOfIds, size(universe)), relResult>;
} 

tuple[list[list[Id]], list[list[Id]]] getBounds(int arity, exact(list[Tuple] tuples)) = <b,b> when list[list[Id]] b := getIndices(arity, tuples);
tuple[list[list[Id]], list[list[Id]]] getBounds(int arity, atMost(list[Tuple] upper)) = <[], ub> when list[list[Id]] ub := getIndices(arity, upper);
tuple[list[list[Id]], list[list[Id]]] getBounds(int arity, atLeastAtMost(list[Tuple] lower, list[Tuple] upper)) = <lb,ub> when list[list[Id]] lb := getIndices(arity, lower), list[list[Id]] ub := getIndices(arity, upper);
      
@memo      
private list[list[Id]] getIndices(int arity, list[Tuple] tuples) {
  list[list[Id]] indices = [];
  for (Tuple t <- tuples) {
     list[Id] idx = [id | id(Id id) <- t.values];
     
     if (size(idx) != arity) {
      throw "Arity definition of id field and nr of ids in tuples do not match";
     }
     
     indices += [idx];
  }
  
  return indices;
}

map[list[Id], map[str, Formula]] createAttributeLookup(relationWithAttributes(str _, int arityOfIds, list[AttributeHeader] headers, RelationalBound bounds), map[list[Id], map[str, Formula]] currentLookup) {
  map[list[Id], map[str, Formula]] partial = createPartialAttributeLookup(arityOfIds, headers, bounds);
  
  for (list[Id] idx <- partial) {
    if (idx in currentLookup) {
      currentLookup[idx] += partial[idx];
    } else {
      currentLookup[idx] = partial[idx];
    }
  }     
  
  return currentLookup;
} 

map[list[Id], map[str, Formula]] createPartialAttributeLookup(int arityOfIds, list[AttributeHeader] headers, exact(list[Tuple] tuples)) = createPartialAttributeLookup(arityOfIds, headers, tuples);
map[list[Id], map[str, Formula]] createPartialAttributeLookup(int arityOfIds, list[AttributeHeader] headers, atMost(list[Tuple] upper)) = createPartialAttributeLookup(arityOfIds, headers, upper);
map[list[Id], map[str, Formula]] createPartialAttributeLookup(int arityOfIds, list[AttributeHeader] headers, atLeastAtMost(list[Tuple] _, list[Tuple] upper)) = createPartialAttributeLookup(arityOfIds, headers, upper);

private map[list[Id], map[str, Formula]] createPartialAttributeLookup(int arityOfIds, list[AttributeHeader] headers, list[Tuple] tuples) {
  map[list[Id], map[str, Formula]] result = ();
  
  for (Tuple t <- tuples) {
    list[Id] idx = [id | id(Id id) <- t.values];
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
                                           
default Formula createAttribute(list[Id] idx, str name, Domain d, Value v) { throw "No attribute creator found for domain \'<d>\' with value \'<v>\'"; } 
                                                                                            
TranslationResult translateProblem(Problem p, Environment env, bool logIndividualFormula = true) {
  FormulaCache formCache = ();
  ExprCache exprCache = ();
  
  Maybe[Formula] formulaLookup(FormulaCacheKey key) {
    if (key in formCache) { return just(formCache[key]); } 
    else {return nothing(); }
  }
  void storeFormula(FormulaCacheKey key, Formula f) { formCache[key] = f; }
  
  Maybe[RelationMatrix] exprLookup(ExprCacheKey key) { 
    if (key in exprCache) { return just(exprCache[key]); } 
    else { return nothing(); }
  }
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
  
  Formula relForm; 
  if (logIndividualFormula) {
    relForm = and({r | AlleFormula f <- p.constraints, bprint("\nTranslating \'<unparse(f)>\' ..."), <Formula r, int time> := bm(f, env, <addAttributeConstraint, addAdditionalCommand, addIntermediateVar, freshIntermediateId>, cache(formulaLookup, storeFormula, exprLookup, storeExpr)), bprint("in <time / 1000000> ms.")});
  } else {
    relForm = and({translateCachedFormula(f, env, <addAttributeConstraint, addAdditionalCommand, addIntermediateVar, freshIntermediateId>, cache(formulaLookup, storeFormula, exprLookup, storeExpr)) | AlleFormula f <- p.constraints});
  }  
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

map[str, RelationMatrix] constructSingleton(str newVarName, Index idx, int size) = (newVarName : <square(1,size), (idx : relOnly(\true()))>);

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
  
  if (m.cells == ()) {
    return \false();
  }
  
  set[Formula] clauses = {};
  
  Formula partial = \false();
  
  for (Index x <- m.cells) {
    Formula clause = or(\not(m.cells[x].relForm), not(partial));
    if (clause == \false()) {
      return \false();
    }
    clauses += clause;  
    partial = \or(partial, m.cells[x].relForm);
  }
  
  clauses += partial;
  
  return \and(clauses);
}

Formula translateFormula(nonEmpty(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix m = translateCachedExpression(expr, env, acf, cache);
  
  set[Formula] clauses = {};
  
  for (Index idx <- m.cells) {
    if (m.cells[idx].relForm == \true()) {
      return \true(); 
    }
    
    clauses += m.cells[idx].relForm;
  } 
  
  return \or(clauses);
}

Formula translateFormula(subset(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix lhs = translateCachedExpression(lhsExpr, env, acf, cache);
  RelationMatrix rhs = translateCachedExpression(rhsExpr, env, acf, cache);
  
  set[Formula] clauses = {};
  for (Index idx <- lhs.cells) {
    Formula partial = \or(not(lhs.cells[idx].relForm), (idx in rhs.cells ? rhs.cells[idx].relForm : \false()));
    if (partial == \false()) {
      return \false();
    }
    
    clauses += partial;   
  }
  
  return \and(clauses);
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

private Environment extEnv(Environment orig, map[str, RelationMatrix] newRelations) = <orig.relations + newRelations, orig.attributes, orig.universe>; 

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

Formula translateFormula(universal(list[VarDeclaration] decls, AlleFormula form), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  bool shortCircuited = false;
  
  set[Formula] clauses = {};
  void accumulate(Formula clause) {
    clauses += clause;
    if (clause == \false()) {
      shortCircuited = true;
    }
  }
  
  bool isShortCircuited() = shortCircuited;
  
  forall(decls, 0, \false(), accumulate, isShortCircuited, form, env, acf, cache);
  
  return \and(clauses);
}
 
 // = translateQuantification(Formula (Formula l, Formula r) { return \or(\not(l), r); }, Formula (set[Formula] clauses) { return  \and(clauses); }, decls, form, env, acf, cache);

//Formula translateFormula(e:existential(list[VarDeclaration] decls, AlleFormula form), Environment env, AdditionalConstraintFunctions acf, Cache cache) 
//  = translateQuantification(Formula (Formula l, Formula r) { return \and(l,r); }, Formula (set[Formula] clauses) { return \or(clauses); }, decls, form, env, acf, cache);

private void forall(list[VarDeclaration] decls, int currentDecl, Formula declConstraints, void (Formula) accumulate, bool () isShortCircuited, AlleFormula form, Environment env, AdditionalConstraintFunctions acf, Cache cache) {
  if (isShortCircuited()) {
    return;
  }
  
  if (currentDecl == size(decls)) {
    return accumulate(\or(declConstraints, translateCachedFormula(form, env, acf, cache)));
  }
  
  RelationMatrix m = translateCachedExpression(decls[currentDecl].binding, env, acf, cache);

  set[Formula] clauses = {};  
  for (Index idx <- m.cells) {
    forall(decls, currentDecl + 1, \or(not(m.cells[idx].relForm), declConstraints),  accumulate, isShortCircuited, form, extEnv(env, constructSingleton(decls[currentDecl].name, idx, m.dim.size)), acf, cache);

    if (isShortCircuited()) {
      return;
    }
  } 
}
    
//  Formula buildForm([], map[str,RelationMatrix] extraBindings) = translateCachedFormula(form, extEnv(env, extraBindings), acf, cache); //substitutes(extEnv(env, extraBindings));
//
//  Formula buildForm([VarDeclaration hd, *VarDeclaration tl], map[str,RelationMatrix] extraBindings) {
//    set[Formula] result = {};
//    
//    RelationMatrix m = translateCachedExpression(hd.binding, extEnv(env, extraBindings), acf, cache);
//
//    for (Index idx <- m.cells) {
//      Formula clause = buildForm(tl, extraBindings + constructSingleton(hd.name, idx, m.dim.size));
//    
//      if (clause == \false() && m.cells[idx].relForm == \true()) {
//        return \false();
//      }
//      
//      result += innerOpper(m.cells[idx].relForm, clause);   
//    }    
//    
//    return outerOpper(result);
//  }
// 
//  Formula result = buildForm(decls, ());
  
  //result = visit(result) {
  //  case substitutes(Environment subs) => translateCachedFormula(form, subs, acf, cache)
  //}
  
//  return result;
//}

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
  
  if (m.cells == ()) {
    return <m.dim, ()>;
  }
  
  for (Index idx <- m.cells) {
    list[Id] key = getVectorIndex(idx, m.dim.arity, env.universe);
    
    if (key notin env.attributes || name notin env.attributes[key]) {
      throw "Attribute \'<name>\' not defined on \'<key>\' ";
    }
    
    m.cells[idx] = relAndAtt(m.cells[idx].relForm, env.attributes[key][name]);
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
 
//RelationMatrix translateExpression(comprehension(list[VarDeclaration] decls, AlleFormula form), Environment env, AdditionalConstraintFunctions acf, Cache cache) {
//  RelationMatrix calculate(Index idx, [], Environment extendedEnv, Formula partialRelForm) {
//    if (partialRelForm == \false()) {
//      return (idx:relOnly(\false()));
//    }
//    
//    return (idx : relOnly(and(partialRelForm, translateCachedFormula(form, extendedEnv, acf, cache))));
//  }
//  
//  RelationMatrix calculate(Index currentIdx, [VarDeclaration hd, *VarDeclaration tl], Environment extendedEnv, Formula partialRelForm) {
//    RelationMatrix relResult = ();
//    
//    RelationMatrix decl = translateCachedExpression(hd.binding, extendedEnv, acf, cache);
//    if (arity(decl) > 1) { throw "Higher order comprehensions are not allowed"; }
//    
//    for (Index idx <- decl.cells) {
//      relResult += calculate(currentIdx + idx, tl, extEnv(extendedEnv, constructSingleton(hd.name, idx)), \and(partialRelForm, decl[idx].relForm));
//    } 
//    
//    return relResult;
//  }
//  
//  return calculate([], decls, env, \true());
//}

default RelationMatrix translateExpression(AlleExpr expr, Environment env, AdditionalConstraintFunctions acf, Cache cache) { throw "Translation of expression \'<expr>\' not supported"; }
