module translation::Translator

import smtlogic::Core;
import translation::AST;
import translation::Environment;
import translation::Relation; 

import translation::Unparser;

import IO; 
import List;

import util::Maybe;
import util::Benchmark;

Formula translateProblem(Problem p, Environment env, bool logIndividualFormula = true) {
  Formula form;

  if (logIndividualFormula) {
    form = and({r | AlleFormula f <- p.constraints, bprint("\nTranslating \'<unparse(f)>\' ..."), <Formula r, int time> := bm(f, env), bprint("in <time / 1000000> ms.")}); //, cache(formulaLookup, storeFormula, exprLookup, storeExpr)
  } else {
    form = and({translateFormula(f, env) | AlleFormula f <- p.constraints}); //, cache(formulaLookup, storeFormula, exprLookup, storeExpr)
  }    
  
  return form; 
}

bool bprint(str line) { 
  print(line);
  return true;
} 

private tuple[Formula, int] bm(AlleFormula f, Environment env) {
  int startTime = cpuTime();
  Formula result = translateFormula(f, env);
  return <result, cpuTime() - startTime>;
}

//map[str, RelationMatrix] constructSingleton(str newVarName, Index idx) = (newVarName : (idx : relOnly(\true())));


Formula translateFormula(empty(AlleExpr expr), Environment env) 
  = \not(translateFormula(nonEmpty(expr), env));


Formula translateFormula(atMostOne(AlleExpr expr), Environment env) {
  Formula empty = translateFormula(empty(expr), env);
  if (empty == \true()) {
    return \true();
  }  
  
  return or(empty, translateFormula(exactlyOne(expr), env));
}


Formula translateFormula(exactlyOne(AlleExpr expr), Environment env) {
  Relation r = translateExpression(expr, env);
  
  if (isEmpty(r)) {
    return \false();
  }
  
  set[Formula] clauses = {};
  set[Formula] attConstraints = {};
  
  Formula partial = \false();
  
  for (Tuple idx <- r.rows) {
    Formula clause = or(\not(r.rows[idx].exists), not(partial));
    if (clause == \false()) {
      return \false();
    }
    
    clauses += clause;  
    attConstraints += getAttributeConstraints(r.rows[idx]);
    
    partial = \or(partial, r.rows[idx].exists);
  }
  
  clauses += partial;
  
  return \and(clauses + attConstraints);
}
 

Formula translateFormula(nonEmpty(AlleExpr expr), Environment env) {
  Relation r = translateExpression(expr, env);
  
  set[Formula] clauses = {};
  set[Formula] attConstraints = {};
  
  for (Tuple idx <- r.rows) {
    if (r.rows[idx].exists == \true()) {
      return \true();
    }
    
    clauses += r.rows[idx].exists;
    attConstraints += getAttributeConstraints(r.rows[idx]);
  } 
  
  return \and(\or(clauses), \and(attConstraints));
}


Formula translateFormula(subset(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env) {
  Relation lhsFull = translateExpression(lhsExpr, env);
  Relation rhsFull = translateExpression(rhsExpr, env);

  if (!unionCompatible(lhsFull,rhsFull)) {
    throw "SUBSET requires union compatible relations";
  }
    
  IndexedRows lhs = index(lhsFull);
  IndexedRows rhs = index(rhsFull);

  set[str] openAttributes = lhsFull.heading<0> - lhs.partialKey;
  
  set[Formula] clauses = {};
  set[Formula] attConstraints = {};
  
  for (Tuple key <- lhs.indexedRows<0>, Row lRow <- lhs.indexedRows[key]) {
    Formula partial = not(lRow.constraints.exists); 
    attConstraints += getAttributeConstraints(lRow.constraints);
        
    if (key in rhs.indexedRows<0>) {
      for (Row rRow <- rhs.indexedRows[key]) {
        Formula tmpAttForm = \true();
        
        for (str att <- openAttributes) {
          tmpAttForm = \and(tmpAttForm, equal(lRow.values[att],rRow.values[att]));
        }
        
        partial = \or(partial, \and(rRow.constraints.exists, tmpAttForm));
        if (partial == \false()) {
          return \false();
        }
        
        clauses += partial;
        attConstraints += getAttributeConstraints(rRow.constraints);
      }
    } else {
      if (partial == \false()) {
        return \false();
      }
      
      clauses += partial;
    }
  }
  
  return \and(clauses + attConstraints);
}
      

Formula translateFormula(equal(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env) {
  Formula l = translateFormula(subset(lhsExpr, rhsExpr), env);
  if (l == \false()) {
    return \false();
  }
  
  return \and(l, translateFormula(subset(rhsExpr, lhsExpr), env));
}

Formula translateFormula(inequal(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env) 
  = translateFormula(negation(equal(lhsExpr, rhsExpr)), env);
  

Formula translateFormula(negation(AlleFormula form), Environment env) 
  = \not(translateFormula(form, env));


Formula translateFormula(conjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env) {
  Formula l = translateFormula(lhsForm, env);
  if (l == \false()) {
    return \false();
  }
  
  return \and(l, translateFormula(rhsForm, env));
}


Formula translateFormula(disjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env) {
  Formula l = translateFormula(lhsForm, env);
  if (l == \true()) {
     return \true();
  }
  
  return \or(l, translateFormula(rhsForm, env));
}


Formula translateFormula(implication(AlleFormula lhsForm, AlleFormula rhsForm), Environment env) {
  Formula l = translateFormula(lhsForm, env);
  if (l == \false()) {
    return \true();
  }
  
  return \or(\not(l), translateFormula(rhsForm, env));
}


Formula translateFormula(equality(AlleFormula lhsForm, AlleFormula rhsForm), Environment env) {
  Formula l = translateFormula(lhsForm, env);
  Formula r = translateFormula(rhsForm, env);
  
  return \or(\and(l,r), \and(\not(l), \not(r)));
}

Formula translateFormula(let(list[VarBinding] bindings, AlleFormula form), Environment env) {
  for (VarBinding b <- bindings) {
    Relation r = translateExpression(b.binding, env);
    env.relations[b.name] = r;
  }
  
  return translateFormula(form, env);
}

Formula translateFormula(universal(list[VarDeclaration] decls, AlleFormula form), Environment env) {
  bool shortCircuited = false;
  
  set[Formula] clauses = {};
  void accumulate(Formula clause) {
    if (clause == \false()) {
      shortCircuited = true;
    }

    clauses += clause;
  }
  
  bool isShortCircuited() = shortCircuited;
  
  forall(decls, 0, \false(), accumulate, isShortCircuited, form, env);
  
  if (shortCircuited) {
    return \false();
  } else {
    return \and(clauses);
  }
}

private void forall(list[VarDeclaration] decls, int currentDecl, Formula declConstraints, void (Formula) accumulate, bool () isShortCircuited, AlleFormula form, Environment env) {
  if (isShortCircuited()) {
    return;
  }
  
  if (currentDecl == size(decls)) {
    return accumulate(\or(declConstraints, translateFormula(form, env)));
  }
  
  Relation r = translateExpression(decls[currentDecl].binding, env);

  for (Tuple t <- r.rows) {
    env.relations[decls[currentDecl].name] = <r.heading,(t:<\true(),r.rows[t].attConstraints>),r.partialKey>;
    forall(decls, currentDecl + 1, \or(not(\and(r.rows[t].exists, r.rows[t].attConstraints)), declConstraints),  accumulate, isShortCircuited, form, env);

    if (isShortCircuited()) {
      return;
    }
  } 
}


Formula translateFormula(existential(list[VarDeclaration] decls, AlleFormula form), Environment env) {
  bool shortCircuited = false;
  
  set[Formula] clauses = {};
  void accumulate(Formula clause) {
    clauses += clause;
    if (clause == \true()) {
      shortCircuited = true;
    }
  }
  
  bool isShortCircuited() = shortCircuited;
  
  exists(decls, 0, \true(), accumulate, isShortCircuited, form, env);
  
  if (shortCircuited) {
    return \true();
  } else {
    return \or(clauses);
  }
}

private void exists(list[VarDeclaration] decls, int currentDecl, Formula declConstraints, void (Formula) accumulate, bool () isShortCircuited, AlleFormula form, Environment env) {
  if (isShortCircuited()) {
    return;
  }
  
  if (currentDecl == size(decls)) {
    return accumulate(\and(declConstraints, translateFormula(form, env)));
  }
  
  Relation r = translateExpression(decls[currentDecl].binding, env);

  for (Tuple t <- r.rows) {
    env.relations[decls[currentDecl].name] = <r.heading,(t:<\true(),r.rows[t].attConstraints>),r.partialKey>;
    exists(decls, currentDecl + 1, \and(\and(r.rows[t].exists, r.rows[t].attConstraints), declConstraints),  accumulate, isShortCircuited, form, env);

    if (isShortCircuited()) {
      return;
    }
  } 
}

default Formula translateFormula(AlleFormula f, Environment env) { throw "Translation of formula \'<f>\' not supported"; }


Relation translateExpression(relvar(str name), Environment env) = env.relations[name];

Relation translateExpression(rename(AlleExpr expr, list[Rename] renames), Environment env) = rename(translateExpression(expr, env), (rn.orig:rn.new | Rename rn <- renames));

Relation translateExpression(project(AlleExpr expr, list[str] attributes), Environment env) = project(translateExpression(expr, env), toSet(attributes));

Relation translateExpression(select(AlleExpr expr, Criteria criteria), Environment env) = select(translateExpression(expr, env), translateCriteria(criteria, env));

Relation translateExpression(union(AlleExpr lhs, AlleExpr rhs), Environment env) = union(translateExpression(lhs,env),translateExpression(rhs,env));

Relation translateExpression(intersection(AlleExpr lhs, AlleExpr rhs), Environment env) = intersect(translateExpression(lhs,env),translateExpression(rhs,env));

Relation translateExpression(difference(AlleExpr lhs, AlleExpr rhs), Environment env) = difference(translateExpression(lhs,env),translateExpression(rhs,env));

Relation translateExpression(product(AlleExpr lhs, AlleExpr rhs), Environment env) = product(translateExpression(lhs,env),translateExpression(rhs,env));

Relation translateExpression(naturalJoin(AlleExpr lhs, AlleExpr rhs), Environment env) = naturalJoin(translateExpression(lhs,env),translateExpression(rhs,env));

Relation translateExpression(transpose(TupleAttributeSelection tas, AlleExpr expr), Environment env) = transpose(translateExpression(expr,env),tas.first, tas.second);

Relation translateExpression(closure(TupleAttributeSelection tas, AlleExpr expr), Environment env) = transitiveClosure(translateExpression(expr,env),tas.first, tas.second);

Relation translateExpression(reflexClosure(TupleAttributeSelection tas, AlleExpr expr), Environment env) = reflexiveTransitiveClosure(translateExpression(expr,env), tas.first, tas.second, identity(env, tas.first, tas.second));

default Relation translateExpression(AlleExpr expr, Environment env) { throw "Translation of expression \'<expr>\' not supported"; }

@memo
Relation identity(Environment env, str first, str second) {
  Heading h = (first:id(),second:id());
  Rows r = ((first:lit(id(k)),second:lit(id(k))):<\true(),\true()> | str k <- env.idDomain);
  
  return <h,r,{first,second}>;
}

Formula (Tuple, Formula) translateCriteria(equal(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr), Environment env) { 
  Term (Tuple,Formula) lhsCrit = translateCriteriaExpr(lhsExpr, env);
  Term (Tuple,Formula) rhsCrit = translateCriteriaExpr(rhsExpr, env);

  Formula translate(Tuple t, Formula f) = equal(lhsCrit(t,f),rhsCrit(t,f));     
  
  return translate; 
} 

Formula (Tuple, Formula) translateCriteria(and(Criteria lhs, Criteria rhs), Environment env) { 
  Formula (Tuple,Formula) lhsCrit = translateCriteria(lhs, env);
  Formula (Tuple,Formula) rhsCrit = translateCriteria(rhs, env);

  Formula translate(Tuple t, Formula f) = and(lhsCrit(t,f),rhsCrit(t,f));     
  
  return translate; 
} 

Formula (Tuple, Formula) translateCriteria(or(Criteria lhs, Criteria rhs), Environment env) { 
  Formula (Tuple,Formula) lhsCrit = translateCriteria(lhs, env);
  Formula (Tuple,Formula) rhsCrit = translateCriteria(rhs, env);

  Formula translate(Tuple t, Formula f) = or(lhsCrit(t,f),rhsCrit(t,f));     
  
  return translate; 
}

Formula (Tuple, Formula) translateCriteria(not(Criteria crit), Environment env) { 
  Formula (Tuple,Formula) crt = translateCriteria(crit, env);

  Formula translate(Tuple t, Formula f) = not(crt(t,f));     
  
  return translate; 
} 

default Formula (Tuple, Formula) translateCriteria(Criteria criteria, Environment env) { throw "Not yet implemented \'<criteria>\'";} 

//data CriteriaExpr
//  | lit(AlleLiteral l)
//  ;

Term (Tuple, Formula) translateCriteriaExpr(att(str name), Environment env) { 
  Term trans(Tuple t, Formula f) {
    if (name notin t) {
      throw "Attribute \'<name>\' not in relation";
    }
    
    return t[name];
  }
  
  return trans; 
} 

default Term (Tuple, Formula) translateCriteriaExpr(CriteriaExpr criteriaExpr, Environment env) { throw "Not yet implemented \'<criteriaExpr>\'";} 

