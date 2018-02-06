module translation::theories::integer::Translator

extend translation::Translator;

import smtlogic::Ints;
import smtlogic::Core;

import translation::theories::integer::AST;
import translation::AST; 

Formula (Tuple) translateCriteria(gt(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr), Environment env) {
  Term (Tuple) lhs = translateCriteriaExpr(lhsExpr, env);
  Term (Tuple) rhs = translateCriteriaExpr(rhsExpr, env);
  
  Formula trans(Tuple t) {
    return gt(lhs(t),rhs(t));
  } 
  
  return trans;
}

Formula (Tuple) translateCriteria(gte(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr), Environment env) {
  Term (Tuple) lhs = translateCriteriaExpr(lhsExpr, env);
  Term (Tuple) rhs = translateCriteriaExpr(rhsExpr, env);
  
  Formula trans(Tuple t) {
    return gte(lhs(t),rhs(t));
  } 
  
  return trans;
}

Formula (Tuple) translateCriteria(lt(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr), Environment env) {
  Term (Tuple) lhs = translateCriteriaExpr(lhsExpr, env);
  Term (Tuple) rhs = translateCriteriaExpr(rhsExpr, env);
  
  Formula trans(Tuple t) {
    return lt(lhs(t),rhs(t));
  } 
  
  return trans;
}

Formula (Tuple)  translateCriteria(lte(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr), Environment env) {
  Term (Tuple) lhs = translateCriteriaExpr(lhsExpr, env);
  Term (Tuple) rhs = translateCriteriaExpr(rhsExpr, env);
  
  Formula trans(Tuple t) {
    return lte(lhs(t),rhs(t));
  } 
  
  return trans;
}

Literal translateLiteral(intLit(int i)) = \int(i);
  
Term (Tuple) translateCriteriaExpr(neg(CriteriaExpr expr), Environment env) {
  Term (Tuple) negExpr = translateCriteriaExpr(expr, env);
  
  Term trans(Tuple t) {
    return neg(negExpr(t));
  } 
  
  return trans;
}

Term (Tuple) translateCriteriaExpr(abs(CriteriaExpr expr), Environment env) {
  Term (Tuple) absExpr = translateCriteriaExpr(expr, env);
  
  Term trans(Tuple t) {
    return abs(absExpr(t));
  } 
  
  return trans;
}

Term (Tuple) translateCriteriaExpr(addition(list[CriteriaExpr] termExprs), Environment env) {
  Term trans(Tuple t) {
    return addition([translateCriteriaExpr(term,env)(t) | CriteriaExpr term <- termExprs]);
  } 
  
  return trans;
}

Term (Tuple) translateCriteriaExpr(multiplication(list[CriteriaExpr] termExprs), Environment env) {
  Term trans(Tuple t) {
    return multiplication([translateCriteriaExpr(term,env)(t) | CriteriaExpr term <- termExprs]);
  } 
  
  return trans;
}

Term (Tuple) translateCriteriaExpr(subtraction(CriteriaExpr lhs, CriteriaExpr rhs), Environment env) 
  = translateCriteriaExpr(addition(lhs, neg(rhs)), env);

Term (Tuple) translateCriteriaExpr(division(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr), Environment env) {
  Term (Tuple) lhs = translateCriteriaExpr(lhsExpr, env);
  Term (Tuple) rhs = translateCriteriaExpr(rhsExpr, env);
  
  Term trans(Tuple t) {
    return division(lhs(t), rhs(t));
  } 
  
  return trans;
}

Term (Tuple) translateCriteriaExpr(modulo(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr), Environment env) {
  Term (Tuple) lhs = translateCriteriaExpr(lhsExpr, env);
  Term (Tuple) rhs = translateCriteriaExpr(rhsExpr, env);
  
  Term trans(Tuple t) {
    return modulo(lhs(t), rhs(t));
  } 
  
  return trans;
}