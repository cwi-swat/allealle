module translation::theories::integer::Translator

import smtlogic::Ints;
import smtlogic::Core;

import translation::Relation;
import translation::Environment;

import translation::theories::integer::AST;
import translation::theories::integer::Environment;

import Map;
import Set;

Formula (Tuple) translateCriteria(gt(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)) {
  Term (Tuple) lhs = translateCriteriaExpr(lhsExpr);
  Term (Tuple) rhs = translateCriteriaExpr(rhsExpr);
  
  Formula trans(Tuple t) {
    return gt(lhs(t),rhs(t));
  } 
  
  return trans;
}

Formula (Tuple) translateCriteria(gte(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)) {
  Term (Tuple) lhs = translateCriteriaExpr(lhsExpr);
  Term (Tuple) rhs = translateCriteriaExpr(rhsExpr);
  
  Formula trans(Tuple t) {
    return gte(lhs(t),rhs(t));
  } 
  
  return trans;
}

Formula (Tuple) translateCriteria(lt(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)) {
  Term (Tuple) lhs = translateCriteriaExpr(lhsExpr);
  Term (Tuple) rhs = translateCriteriaExpr(rhsExpr);
  
  Formula trans(Tuple t) {
    return lt(lhs(t),rhs(t));
  } 
  
  return trans;
}

Formula (Tuple)  translateCriteria(lte(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)) {
  Term (Tuple) lhs = translateCriteriaExpr(lhsExpr);
  Term (Tuple) rhs = translateCriteriaExpr(rhsExpr);
  
  Formula trans(Tuple t) {
    return lte(lhs(t),rhs(t));
  } 
  
  return trans;
}

Literal translateLiteral(intLit(int i)) = \int(i);
  
Term (Tuple) translateCriteriaExpr(neg(CriteriaExpr expr)) {
  Term (Tuple) negExpr = translateCriteriaExpr(expr);
  
  Term trans(Tuple t) {
    return neg(negExpr(t));
  } 
  
  return trans;
}

Term (Tuple) translateCriteriaExpr(abs(CriteriaExpr expr)) {
  Term (Tuple) absExpr = translateCriteriaExpr(expr);
  
  Term trans(Tuple t) {
    return abs(absExpr(t));
  } 
  
  return trans;
}

Term (Tuple) translateCriteriaExpr(addition(list[CriteriaExpr] termExprs)) {
  Term trans(Tuple t) {
    return addition([translateCriteriaExpr(term)(t) | CriteriaExpr term <- termExprs]);
  } 
  
  return trans;
}

Term (Tuple) translateCriteriaExpr(multiplication(list[CriteriaExpr] termExprs)) {
  Term trans(Tuple t) {
    return multiplication([translateCriteriaExpr(term)(t) | CriteriaExpr term <- termExprs]);
  } 
  
  return trans;
}

Term (Tuple) translateCriteriaExpr(subtraction(CriteriaExpr lhs, CriteriaExpr rhs)) 
  = translateCriteriaExpr(addition(lhs, neg(rhs)));

Term (Tuple) translateCriteriaExpr(division(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)) {
  Term (Tuple) lhs = translateCriteriaExpr(lhsExpr);
  Term (Tuple) rhs = translateCriteriaExpr(rhsExpr);
  
  Term trans(Tuple t) {
    return division(lhs(t), rhs(t));
  } 
  
  return trans;
}

Term (Tuple) translateCriteriaExpr(modulo(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)) {
  Term (Tuple) lhs = translateCriteriaExpr(lhsExpr);
  Term (Tuple) rhs = translateCriteriaExpr(rhsExpr);
  
  Term trans(Tuple t) {
    return modulo(lhs(t), rhs(t));
  } 
  
  return trans;
}

Relation translateAggregateFunction(avg(str attName), str bindTo, Relation r, Environment env) { 
  Relation sum = translateAggregateFunctionDef(aggFuncDef(sum(attName), "<bindTo>_sum"), r, env);
  Relation count = translateAggregateFunctionDef(aggFuncDef(count(), "<bindTo>_count"), r, env);

  Formula exsts = (size(sum.rows) > 0) ? \true() : \false();
  if (exsts == \false()) {
    return <(bindTo:intDom()), (), {}>;
  }

  Term avgVar = env.newVar(bindTo, Sort::\int());
  
  Formula attConstraints = \true();
  for (Tuple sumTuple <- sum.rows, Tuple countTuple <- count.rows) {
    attConstraints = \and(equal(avgVar, division(sumTuple["<bindTo>_sum"], countTuple["<bindTo>_count"])), \and(sum.rows[sumTuple].attConstraints, count.rows[countTuple].attConstraints));
  }
  
  return <(bindTo:intDom()), ((bindTo:avgVar):<exsts, attConstraints>), {}>;      
}

Relation translateAggregateFunction(count(), str bindTo, Relation r, Environment env) { 
  list[Term] terms = [];
  
  for (Tuple t <- r.rows) {
    terms += ite(together(r.rows[t]), lit(\int(1)), lit(\int(0)));
  }
    
  Term countVar = env.newVar(bindTo, Sort::\int());
  Term countTerm = terms == [] ? lit(\int(0)) : addition(terms);
  
  return <(bindTo:intDom()), ((bindTo:countVar):<\true(), equal(countVar, countTerm)>), {}>;
}

Relation translateAggregateFunction(sum(str att), str bindTo, Relation r, Environment env) { 
  list[Term] terms = [];
  
  for (Tuple t <- r.rows) {
    terms += ite(together(r.rows[t]), t[att], lit(\int(0)));
  }
  
  Term sumVar = env.newVar(bindTo, Sort::\int());
  
  return <(bindTo:intDom()), ((bindTo:sumVar):<\true(), equal(sumVar, addition(terms))>), {}>;
}

Relation emptyRel(Heading h) = <h, (), {}>;

Relation translateAggregateFunction(min(str att), str bindTo, Relation r, Environment env) { 
  if (size(r.rows) == 0) {
    return emptyRel((bindTo:intDom()));
  }
  
  Term initialTerm = lit(\int(0));
  Formula rowsExists = \false();
  
  for (Tuple t <- r.rows) {
    initialTerm = ite(together(r.rows[t]), t[att], initialTerm);
    rowsExists = \or(rowsExists, together(r.rows[t])); 
  }
  
  if (rowsExists == \false()) {
    return emptyRel((bindTo:intDom()));
  }
  
  Term minTerm = initialTerm;  
  for (Tuple t <- r.rows) {
    minTerm = ite(\and(together(r.rows[t]), lt(t[att],minTerm)), t[att], minTerm);
  }
  
  Term minVar = env.newVar(bindTo, Sort::\int());
  
  return <(bindTo:intDom()), ((bindTo:minVar):<\true(), equal(minVar, minTerm)>), {}>;
}

Relation translateAggregateFunction(max(str att), str bindTo, Relation r, Environment env) { 
  if (size(r.rows) == 0) {
    return emptyRel((bindTo:intDom()));
  }
  
  Term initialTerm = lit(\int(0));
  Formula rowsExists = \false();
  
  for (Tuple t <- r.rows) {
    initialTerm = ite(together(r.rows[t]), t[att], initialTerm);
    rowsExists = \or(rowsExists, together(r.rows[t]));
  }
  
  if (rowsExists == \false()) {
    return emptyRel((bindTo:intDom()));
  }
  
  Term maxTerm = initialTerm;  
  for (Tuple t <- r.rows) {
    maxTerm = ite(\and(together(r.rows[t]), gt(t[att],maxTerm)), t[att], maxTerm);
  }
  
  Term maxVar = env.newVar(bindTo, Sort::\int());
  
  return <(bindTo:intDom()), ((bindTo:maxVar):<\true(), equal(maxVar, maxTerm)>), {}>;
}
