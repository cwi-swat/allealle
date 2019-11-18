module translation::Translator

import smtlogic::Core;

import translation::AST;
import translation::Environment;
import translation::Relation; 
import translation::Unparser;

extend translation::theories::integer::Translator;
extend translation::theories::string::Translator;

import IO; 
import List;
import Map;
import Set;

import util::Maybe;
import util::Benchmark;

alias TranslationResult = tuple[Formula form, list[Command] cmds];

TranslationResult translateProblem(Problem p, Environment env, bool logIndividualFormula = false) {
  void log(str message) {
    if (logIndividualFormula) print(message);
  }
  
  Formula form = \true();
  list[Command] cmds = []; 
  
  for (AlleFormula f <- p.constraints) {
    log("\nTranslating \'<unparse(f)>\' ...");
    tuple[Formula f, int time] transResult = bm(f, env);
    log("in <transResult.time / 1000000> ms.");
    
    form = and(form,transResult.f);
    
    if (form == \false()) {
      log("Result of last translation is false. Shortcircuiting");
      return <\false(),[]>;
    }
  }
  
  if (just(ObjectiveSection objSec) := p.objectiveSec) {
    cmds += translateOptimizationPriority(objSec.prio);
  
    for (Objective obj <- objSec.objs) {
      map[Command,Formula] trans = translateObjective(obj,env);
      for (Command c <- trans) {
        if (logIndividualFormula) {
          println("Translating \'<unparse(obj)>\'");
        }
        
        form = and(form, trans[c]);
        cmds += c;
      }
    } 
  }    
  
  return <form, cmds>; 
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

Formula translateFormula(predCall(str predName, list[AlleExpr] args), Environment env) {
  AllePredicate pred = env.predicates[predName];
  
  list[VarBinding] bindings = [varBinding(pred.params[i].name, args[i]) | int i <- [0..size(pred.params)]];
  
  return translateFormula(let(bindings, pred.form), env);
}

Formula translateFormula(empty(AlleExpr expr), Environment env) {
   return \not(translateFormula(nonEmpty(expr), env));
}


Formula translateFormula(atMostOne(AlleExpr expr), Environment env) {
  Formula emp = translateFormula(empty(expr), env);
  if (emp == \true()) {
    return \true();
  }  
  
  return or(emp, translateFormula(exactlyOne(expr), env));
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
    Formula clause = or(\not(together(r.rows[idx])), not(partial));
    if (clause == \false()) {
      return \false();
    }
    
    clauses += clause;  
    
    partial = \or(partial, together(r.rows[idx]));
  }
  
  clauses += partial;

  return \and(clauses);
}
 

Formula translateFormula(nonEmpty(AlleExpr expr), Environment env) {
  Relation r = translateExpression(expr, env);
  
  set[Formula] clauses = {};
  
  for (Tuple idx <- r.rows) {
    if (together(r.rows[idx]) == \true()) {
      return \true();
    }
    
    clauses += together(r.rows[idx]); 
  } 
  
  return \or(clauses);
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
  
  set[Tuple] lhsKeys = lhs.indexedRows<0>;
  set[Tuple] rhsKeys = rhs.indexedRows<0>;
  
  for (Tuple key <- lhsKeys, Row lRow <- lhs.indexedRows[key]) {
    Formula partial = not(together(lRow.constraints)); 
        
    if (key in rhsKeys) {
      for (Row rRow <- rhs.indexedRows[key]) {
        Formula tmpAttForm = \true();
        
        for (str att <- openAttributes) {
          tmpAttForm = \and(tmpAttForm, equal(lRow.values[att],rRow.values[att]));
        }
        
        //partial = \or(partial, \and(rRow.constraints.exists, tmpAttForm));
        partial = \or(partial, \and(together(rRow.constraints), tmpAttForm));
        
      }
      clauses += partial;
    } else {
      clauses += partial;
    }
    
    //if (partial == \false()) {
    //  return \false();
    //}
  }
  
  return \and(clauses);
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

Formula translateFormula(\filter(AlleExpr expr, Criteria crit), Environment env) 
  = translateFormula(universal([varDecl("_elem", expr)], nonEmpty(select(relvar("_elem"), crit))), env);

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

  int i = 1;
  
  for (Tuple t <- r.rows) {
    //println("forall <i> of <nrOfTuples>"); 
    env.relations[decls[currentDecl].name] = <r.heading,(t:<\true(),r.rows[t].attConstraints>),r.partialKey>;
    forall(decls, currentDecl + 1, \or(not(together(r.rows[t])), declConstraints),  accumulate, isShortCircuited, form, env);

    if (isShortCircuited()) {
      return;
    }
    
    i += 1;
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
    exists(decls, currentDecl + 1, \and(together(r.rows[t]), declConstraints),  accumulate, isShortCircuited, form, env);

    if (isShortCircuited()) {
      return;
    }
  } 
}

default Formula translateFormula(AlleFormula f, Environment _) { throw "Translation of formula \'<f>\' not supported"; }

Relation translateExpression(relvar(str name), Environment env) = env.relations[name];

Relation translateExpression(rename(AlleExpr expr, list[Rename] renames), Environment env) = rename(translateExpression(expr, env), (rn.orig:rn.new | Rename rn <- renames));

Relation translateExpression(project(AlleExpr expr, list[str] attributes), Environment env) = project(translateExpression(expr, env), toSet(attributes));

Relation translateExpression(aggregate(AlleExpr expr, list[AggregateFunctionDef] funcs), Environment env) = aggregate(translateExpression(expr, env), funcs, env);

private Relation aggregate(Relation r, list[AggregateFunctionDef] funcs, Environment env) {
  Relation cross([Relation r]) = r;
  default Relation cross([Relation head, *Relation tail]) = product(head, cross(tail));
  
  list[Relation] aggregatedResults = [];
  for (AggregateFunctionDef def <- funcs) {
    aggregatedResults += translateAggregateFunctionDef(def, r, env);
  }
  
  return cross(aggregatedResults);
}

Relation translateExpression(groupedAggregate(AlleExpr expr, list[str] gb, list[AggregateFunctionDef] funcs), Environment env) { 
  Relation r = translateExpression(expr, env);
  
  map[Relation,Relation] groupedRel = groupBy(r, gb);
  Rows rows = ();
  Heading newHeading = ();
   
  for (Relation partial <- groupedRel) {
    Relation p = product(partial, aggregate(groupedRel[partial], funcs, env));
    
    rows += p.rows; 
    newHeading = p.heading;
  }
  
  return <newHeading, rows, toSet(gb)>;
}

Relation translateExpression(select(AlleExpr expr, Criteria criteria), Environment env) = select(translateExpression(expr, env), translateCriteria(criteria));

Relation translateExpression(union(AlleExpr lhs, AlleExpr rhs), Environment env) = union(translateExpression(lhs,env),translateExpression(rhs,env));

Relation translateExpression(intersection(AlleExpr lhs, AlleExpr rhs), Environment env) = intersect(translateExpression(lhs,env),translateExpression(rhs,env));

Relation translateExpression(difference(AlleExpr lhs, AlleExpr rhs), Environment env) = difference(translateExpression(lhs,env),translateExpression(rhs,env));

Relation translateExpression(product(AlleExpr lhs, AlleExpr rhs), Environment env) = product(translateExpression(lhs,env),translateExpression(rhs,env));

Relation translateExpression(naturalJoin(AlleExpr lhs, AlleExpr rhs), Environment env) = naturalJoin(translateExpression(lhs,env),translateExpression(rhs,env));

Relation translateExpression(transpose(TupleAttributeSelection tas, AlleExpr expr), Environment env) = transpose(translateExpression(expr,env),tas.first, tas.second);

Relation translateExpression(closure(TupleAttributeSelection tas, AlleExpr expr), Environment env) = transitiveClosure(translateExpression(expr,env),tas.first, tas.second);

Relation translateExpression(reflexClosure(TupleAttributeSelection tas, AlleExpr expr), Environment env) = reflexiveTransitiveClosure(translateExpression(expr,env), tas.first, tas.second, identity(env, tas.first, tas.second));

@memo
Relation translateExpression(comprehension(list[VarDeclaration] decls, AlleFormula form), Environment env) { 
  Heading mergedHeading = ();
  set[str] mergedPartialKey = {};
  
  Rows translateForm([], Row cur, Environment extEnv) =  (cur.values : <\and(cur.constraints.exists, translateFormula(form, extEnv)), cur.constraints.attConstraints>);
	Rows translateForm([<str var, Relation r>, *tl], Row cur, Environment extEnv) {
	  Rows newRows = ();
	  
	  for (Tuple t <- r.rows) {
	    Constraints tc = r.rows[t];

	    Row joined = <cur.values + t, <\and(cur.constraints.exists,tc.exists), \and(cur.constraints.attConstraints, tc.attConstraints)>>; 
	    extEnv.relations += ("<var>" : <r.heading, (t: <tc.exists, tc.attConstraints>), r.partialKey>);
	    
	    newRows += translateForm(tl, joined, extEnv);
	  }  
	  
	  return newRows; 
	}

  Relation transl(AlleExpr expr, Environment extEnv) {
    Relation r = translateExpression(expr, extEnv);
    mergedHeading += r.heading;
    mergedPartialKey += r.partialKey;
    return r;
  }
	 	
  lrel[str,Relation] translateDecls([VarDeclaration d], Environment extEnv) { 
    return [<"<d.name>",transl(d.binding, extEnv)>];
  }  	 	
  
  lrel[str,Relation] translateDecls([VarDeclaration hd, *VarDeclaration tl], Environment extEnv) {
   Relation r = transl(hd.binding, extEnv);
   extEnv.relations += ("<hd.name>" : r);
   return [<"<hd.name>",r>] + translateDecls(tl, extEnv); 
  }     
	
	lrel[str,Relation] translDecls = translateDecls(decls, env);
	
  return <mergedHeading, translateForm(translDecls, <(),<\true(),\true()>>, env), mergedPartialKey>;
}

default Relation translateExpression(AlleExpr expr, Environment _) { throw "Translation of expression \'<expr>\' not supported"; }

alias AggregateFunctionResult = tuple[Domain bindToDomain, Term resultVar, bool hasStaticInitial, Term initialTerm, Term (Row, Term) buildInitialTerm, Term (Row, Term) buildAggregateTerm, Formula (Formula) buildExists];
 
Relation translateAggregateFunctionDef(AggregateFunctionDef def, Relation r, Environment env) = translateAggregateFunction(def.func, def.bindTo, r, env); 

default Relation translateAggregateFunction(AggregateFunction f, str _, Relation _, Environment _) { throw "Translation of aggregate function \'<f>\' not supported"; }

@memo
Relation identity(Environment env, str first, str second) {
  Heading h = (first:id(),second:id());
  Rows r = ((first:lit(id(k)),second:lit(id(k))):<\true(),\true()> | str k <- env.idDomain);
  return <h,r,{first,second}>;
} 

Formula (Tuple) translateCriteria(equal(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)) { 
  Term (Tuple) lhsCrit = translateCriteriaExpr(lhsExpr);
  Term (Tuple) rhsCrit = translateCriteriaExpr(rhsExpr);

  Formula translate(Tuple t) = equal(lhsCrit(t),rhsCrit(t));     
  
  return translate; 
} 

Formula (Tuple) translateCriteria(inequal(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)) 
  = translateCriteria(not(equal(lhsExpr, rhsExpr)));

Formula (Tuple) translateCriteria(and(Criteria lhs, Criteria rhs)) { 
  Formula (Tuple) lhsCrit = translateCriteria(lhs);
  Formula (Tuple) rhsCrit = translateCriteria(rhs);

  Formula translate(Tuple t) {
    Formula lhsForm = lhsCrit(t);
    if (lhsForm == \false()) {
      return \false();
    } else {
      return and(lhsForm,rhsCrit(t));     
    }
  }
    
  return translate; 
} 

Formula (Tuple) translateCriteria(or(Criteria lhs, Criteria rhs)) { 
  Formula (Tuple) lhsCrit = translateCriteria(lhs);
  Formula (Tuple) rhsCrit = translateCriteria(rhs);

  Formula translate(Tuple t) { 
    Formula lhsForm = lhsCrit(t);
    if (lhsForm == \true()) {
      return \true();
    } else {
      return or(lhsForm,rhsCrit(t));     
    }
  }
  
  return translate; 
}

Formula (Tuple) translateCriteria(not(Criteria crit)) { 
  Formula (Tuple) crt = translateCriteria(crit);

  Formula translate(Tuple t) = not(crt(t));     
  
  return translate; 
} 

default Formula (Tuple) translateCriteria(Criteria criteria) { throw "Not yet implemented \'<criteria>\'";} 

Term (Tuple) translateCriteriaExpr(att(str name)) { 
  Term trans(Tuple t) {
    if (name notin t) {
      throw "Attribute \'<name>\' not in relation";
    }
    
    return t[name];
  }
  
  return trans; 
} 

Term (Tuple) translateCriteriaExpr(litt(AlleLiteral l)) {  
  Term trans(Tuple _) = lit(translateLiteral(l));
  
  return trans;
}

Term (Tuple) translateCriteriaExpr(ite(Criteria condition, CriteriaExpr thn, CriteriaExpr els)) { 
  Formula (Tuple) condCrit = translateCriteria(condition);
  Term (Tuple) thnCrit     = translateCriteriaExpr(thn);
  Term (Tuple) elsCrit     = translateCriteriaExpr(els);

  Term translate(Tuple t) = ite(condCrit(t), thnCrit(t), elsCrit(t));     
  
  return translate; 
} 

default Term (Tuple) translateCriteriaExpr(CriteriaExpr criteriaExpr) { throw "Not yet implemented \'<criteriaExpr>\'";} 

Command translateOptimizationPriority(ObjectivePriority prio) = setOption(optimizationPriority(translateOptPrioStrategy(prio)));

OptPriority translateOptPrioStrategy(lex()) = lexicographic();
OptPriority translateOptPrioStrategy(pareto()) = smtlogic::Core::pareto();
OptPriority translateOptPrioStrategy(independent()) = smtlogic::Core::independent();

map[Command,Formula] translateObjective(Objective obj, Environment env) {
  Relation r = translateExpression(obj.expr,env);
  
  set[str] nonIdFields = getNonIdFields(r.heading);
  
  if (size(nonIdFields) != 1) {
    throw "Can only maximize on a relation with one non-id attribute";
  }
  
  map[Command,Formula] cmds = ();
  
  for (Tuple t <- r.rows, str attName := getOneFrom(nonIdFields)) {
    //Term objectiveVar = env.newVar("_objective_<attName>", domain2Sort(r.heading[attName]));
    //cmds[translateObjectiveFunction(obj, objectiveVar)] = implies(together(r.rows[t]), equal(objectiveVar, t[attName]));
    cmds[translateObjectiveFunction(obj, t[attName])] = implies(r.rows[t].exists, r.rows[t].attConstraints);
  }
  
  return cmds;
}

Command translateObjectiveFunction(maximize(AlleExpr _), Term t) = maximize(t);
Command translateObjectiveFunction(minimize(AlleExpr _), Term t) = minimize(t);

Literal translateLiteral(idLit(Id i)) = id(i);

default Literal translateLiteral(AlleLiteral l) { throw "Unable to translate literal \'<l>\'. Not yet implemented"; }
