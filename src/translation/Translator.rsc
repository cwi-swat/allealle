module translation::Translator

import logic::Propositional;
import translation::AST;
import translation::Environment;
import translation::Binder; 
import translation::Unparser;

//import logic::CBCFactory;

import IO; 
import List;

import util::Maybe;
import util::Benchmark;

alias TranslationResult = tuple[Formula relationalFormula, Formula attributeFormula, set[Formula] intermediateVars, list[Command] additionalCommands];
                                                                                             
TranslationResult translateProblem(Problem p, Environment env, bool logIndividualFormula = true) {
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
    relForm = and({r | AlleFormula f <- p.constraints, bprint("\nTranslating \'<unparse(f)>\' ..."), <Formula r, int time> := bm(f, env, <addAttributeConstraint, addAdditionalCommand, addIntermediateVar, freshIntermediateId>), bprint("in <time / 1000000> ms.")}); //, cache(formulaLookup, storeFormula, exprLookup, storeExpr)
  } else {
    relForm = and({translateFormula(f, env, <addAttributeConstraint, addAdditionalCommand, addIntermediateVar, freshIntermediateId>) | AlleFormula f <- p.constraints}); //, cache(formulaLookup, storeFormula, exprLookup, storeExpr)
  }    
  Formula attForm = and(attributeConstraints);
  
  return <relForm, attForm, intermediateVars, additionalCommands>; 
}

bool bprint(str line) { 
  print(line);
  return true;
}

private tuple[Formula, int] bm(AlleFormula f, Environment env, AdditionalConstraintFunctions acf) {
  int startTime = cpuTime();
  Formula result = translateFormula(f, env, acf);
  return <result, cpuTime() - startTime>;
}

map[str, RelationMatrix] constructSingleton(str newVarName, Index idx) = (newVarName : (idx : relOnly(\true())));


Formula translateFormula(empty(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) 
  = \not(translateFormula(nonEmpty(expr), env, acf));


Formula translateFormula(atMostOne(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) {
  Formula empty = translateFormula(empty(expr), env, acf);
  if (empty == \true()) {
    return \true();
  }  
  
  return or(empty, translateFormula(exactlyOne(expr), env, acf));
}


Formula translateFormula(exactlyOne(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) {
  RelationMatrix m = translateExpression(expr, env, acf);
  
  if (m == ()) {
    return \false();
  }
  
  set[Formula] clauses = {};
  
  Formula partial = \false();
  
  for (Index x <- m) {
    Formula clause = or(\not(m[x].relForm), not(partial));
    if (clause == \false()) {
      return \false();
    }
    clauses += clause;  
    partial = \or(partial, m[x].relForm);
  }
  
  clauses += partial;
  
  return \and(clauses);
}
 

Formula translateFormula(nonEmpty(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) {
  RelationMatrix m = translateExpression(expr, env, acf);
  
  set[Formula] clauses = {};
  
  for (Index idx <- m) {
    if (m[idx].relForm == \true()) {
      return \true();
    }
    
    clauses += m[idx].relForm;
  } 
  
  return \or(clauses);
}


Formula translateFormula(subset(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) {
  RelationMatrix lhs = translateExpression(lhsExpr, env, acf);
  RelationMatrix rhs = translateExpression(rhsExpr, env, acf);
  
  set[Formula] clauses = {};
  for (Index idx <- lhs) {
    Formula partial = \or(not(lhs[idx].relForm), (idx in rhs ? rhs[idx].relForm : \false()));
    if (partial == \false()) {
      return \false();
    }
    
    clauses += partial;   
  }
  
  return \and(clauses);
}
     

Formula translateFormula(equal(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) {
  Formula l = translateFormula(subset(lhsExpr, rhsExpr), env, acf);
  if (l == \false()) {
    return \false();
  }
  
  return \and(l, translateFormula(subset(rhsExpr, lhsExpr), env, acf));
}

Formula translateFormula(inequal(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) 
  = translateFormula(negation(equal(lhsExpr, rhsExpr)), env, acf);
  

Formula translateFormula(negation(AlleFormula form), Environment env, AdditionalConstraintFunctions acf) 
  = \not(translateFormula(form, env, acf));


Formula translateFormula(conjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, AdditionalConstraintFunctions acf) {
  Formula l = translateFormula(lhsForm, env, acf);
  if (l == \false()) {
    return \false();
  }
  
  return \and(l, translateFormula(rhsForm, env, acf));
}


Formula translateFormula(disjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, AdditionalConstraintFunctions acf) {
  Formula l = translateFormula(lhsForm, env, acf);
  if (l == \true()) {
     return \true();
  }
  
  return \or(l, translateFormula(rhsForm, env, acf));
}


Formula translateFormula(implication(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, AdditionalConstraintFunctions acf) {
  Formula l = translateFormula(lhsForm, env, acf);
  if (l == \false()) {
    return \true();
  }
  
  return \or(\not(l), translateFormula(rhsForm, env, acf));
}


Formula translateFormula(equality(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, AdditionalConstraintFunctions acf) {
  Formula l = translateFormula(lhsForm, env, acf);
  Formula r = translateFormula(rhsForm, env, acf);
  
  return \or(\and(l,r), \and(\not(l), \not(r)));
}

private Environment extEnv(Environment orig, map[str, RelationMatrix] newRelations) = <orig.relations + newRelations, orig.attributes, orig.idDomain>; 

Formula translateFormula(let(list[VarDeclaration] decls, AlleFormula form), Environment env, AdditionalConstraintFunctions acf) {
  Environment extendedEnv = env;
  
  for (VarDeclaration decl <- decls) {
    RelationMatrix b = translateExpression(decl.binding, extendedEnv, acf);
    extendedEnv = extEnv(extendedEnv, (decl.name : b));
  }
  
  return translateFormula(form, extendedEnv, acf);
}


Formula translateFormula(universal(list[VarDeclaration] decls, AlleFormula form), Environment env, AdditionalConstraintFunctions acf) {
  bool shortCircuited = false;
  
  set[Formula] clauses = {};
  void accumulate(Formula clause) {
    clauses += clause;
    if (clause == \false()) {
      shortCircuited = true;
    }
  }
  
  bool isShortCircuited() = shortCircuited;
  
  forall(decls, 0, \false(), accumulate, isShortCircuited, form, env, acf);
  
  return \and(clauses);
}

private void forall(list[VarDeclaration] decls, int currentDecl, Formula declConstraints, void (Formula) accumulate, bool () isShortCircuited, AlleFormula form, Environment env, AdditionalConstraintFunctions acf) {
  if (isShortCircuited()) {
    return;
  }
  
  if (currentDecl == size(decls)) {
    return accumulate(\or(declConstraints, translateFormula(form, env, acf)));
  }
  
  RelationMatrix m = translateExpression(decls[currentDecl].binding, env, acf);

  set[Formula] clauses = {};  
  for (Index idx <- m) {
    forall(decls, currentDecl + 1, \or(not(m[idx].relForm), declConstraints),  accumulate, isShortCircuited, form, extEnv(env, constructSingleton(decls[currentDecl].name, idx)), acf);

    if (isShortCircuited()) {
      return;
    }
  } 
}


Formula translateFormula(existential(list[VarDeclaration] decls, AlleFormula form), Environment env, AdditionalConstraintFunctions acf) {
  bool shortCircuited = false;
  
  set[Formula] clauses = {};
  void accumulate(Formula clause) {
    clauses += clause;
    if (clause == \true()) {
      shortCircuited = true;
    }
  }
  
  bool isShortCircuited() = shortCircuited;
  
  exists(decls, 0, \true(), accumulate, isShortCircuited, form, env, acf);
  
  return \or(clauses);
}

private void exists(list[VarDeclaration] decls, int currentDecl, Formula declConstraints, void (Formula) accumulate, bool () isShortCircuited, AlleFormula form, Environment env, AdditionalConstraintFunctions acf) {
  if (isShortCircuited()) {
    return;
  }
  
  if (currentDecl == size(decls)) {
    return accumulate(\and(declConstraints, translateFormula(form, env, acf)));
  }
  
  RelationMatrix m = translateExpression(decls[currentDecl].binding, env, acf);

  set[Formula] clauses = {};  
  for (Index idx <- m) {
    exists(decls, currentDecl + 1, \and(m[idx].relForm, declConstraints),  accumulate, isShortCircuited, form, extEnv(env, constructSingleton(decls[currentDecl].name, idx)), acf);

    if (isShortCircuited()) {
      return;
    }
  } 
}

default Formula translateFormula(AlleFormula f, Environment env, AdditionalConstraintFunctions acf) { throw "Translation of formula \'<f>\' not supported"; }


RelationMatrix translateExpression(variable(str name), Environment env, AdditionalConstraintFunctions acf) = env.relations[name];


RelationMatrix translateExpression(attributeLookup(AlleExpr e, str name), Environment env, AdditionalConstraintFunctions acf) {
  RelationMatrix m = translateExpression(e, env, acf);
  
  if (m == ()) {
    return ();
  }
  
  RelationMatrix result = ();
  
  for (Index idx <- m) {
    //if (idx notin env.attributes || name notin env.attributes[idx]) {
    //  throw "Attribute \'<name>\' not defined on \'<idx>\' ";
    //}

    if (idx in env.attributes && name in env.attributes[idx]) {
      result[idx] = relAndAtt(m[idx].relForm, env.attributes[idx][name]);
    }
    
    //m[idx] = relAndAtt(m[idx].relForm, env.attributes[idx][name]);
  }
  
  return result;   
}


@memo 
RelationMatrix universe(Environment env) = ([id] : relOnly(\true()) | Id id <- env.idDomain);

@memo
RelationMatrix identity(Environment env) = ([id,id] : relOnly(\true()) | Id id <- env.idDomain);


RelationMatrix translateExpression(transpose(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) = transpose(m)
  when RelationMatrix m := translateExpression(expr, env, acf); 


RelationMatrix translateExpression(closure(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) = transitiveClosure(m)
  when RelationMatrix m := translateExpression(expr, env, acf);


RelationMatrix translateExpression(reflexClosure(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) = reflexiveTransitiveClosure(m, identity(env))
  when RelationMatrix m := translateExpression(expr, env, acf);


RelationMatrix translateExpression(union(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = or(lhs,rhs)  
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

RelationMatrix translateExpression(override(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = override(lhs,rhs)  
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

RelationMatrix translateExpression(intersection(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = and(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);


RelationMatrix translateExpression(difference(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = difference(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);


RelationMatrix translateExpression(\join(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = dotJoin(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf), 
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);


RelationMatrix translateExpression(accessorJoin(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateExpression(\join(rhsExpr, lhsExpr), env, acf);


RelationMatrix translateExpression(product(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = product(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf), 
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);


RelationMatrix translateExpression(ifThenElse(AlleFormula caseForm, AlleExpr thenExpr, AlleExpr elseExpr), Environment env, AdditionalConstraintFunctions acf) = ite(\case, then, \else)
  when Formula \case := translateFormula(caseForm, env, acf),
       RelationMatrix then := translateExpression(thenExpr, env, acf),
       RelationMatrix \else := translateExpression(elseExpr, env, acf);


RelationMatrix translateExpression(comprehension(list[VarDeclaration] decls, AlleFormula form), Environment env, AdditionalConstraintFunctions acf) {
  RelationMatrix calculate(Index idx, [], Environment extendedEnv, Formula partialRelForm) {
    if (partialRelForm == \false()) {
      return (idx:relOnly(\false()));
    }
    
    return (idx : relOnly(and(partialRelForm, translateFormula(form, extendedEnv, acf))));
  }
  
  RelationMatrix calculate(Index currentIdx, [VarDeclaration hd, *VarDeclaration tl], Environment extendedEnv, Formula partialRelForm) {
    RelationMatrix relResult = ();
    
    RelationMatrix decl = translateExpression(hd.binding, extendedEnv, acf);
    if (arity(decl) > 1) { throw "Higher order comprehensions are not allowed"; }
    
    for (Index idx <- decl) {
      relResult += calculate(currentIdx + idx, tl, extEnv(extendedEnv, constructSingleton(hd.name, idx)), \and(partialRelForm, decl[idx].relForm));
    } 
    
    return relResult;
  }
  
  return calculate([], decls, env, \true());
}

default RelationMatrix translateExpression(AlleExpr expr, Environment env, AdditionalConstraintFunctions acf) { throw "Translation of expression \'<expr>\' not supported"; }
