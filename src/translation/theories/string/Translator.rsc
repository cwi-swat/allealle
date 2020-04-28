module translation::theories::string::Translator

import smtlogic::Strings;

import translation::Relation;
import translation::theories::string::AST;

import Map;
import Set;

Literal translateLiteral(strLit(str s)) = \str(s);
  
Term (Tuple) translateCriteriaExpr(strLength(CriteriaExpr expr)) {
  Term (Tuple) strExpr = translateCriteriaExpr(expr);

  Term trans(Tuple t) {
    return strLength(strExpr(t));
  } 
  
  return trans;
}  

Term (Tuple) translateCriteriaExpr(strToInt(CriteriaExpr expr)) {  
  Term (Tuple) strExpr = translateCriteriaExpr(expr);

  Term trans(Tuple t) {
    return strToInt(strExpr(t));
  } 
  
  return trans;
}

Term (Tuple) translateCriteriaExpr(intToStr(CriteriaExpr expr)) {  
  Term (Tuple) strExpr = translateCriteriaExpr(expr);

  Term trans(Tuple t) {
    return intToStr(strExpr(t));
  } 
  
  return trans;
}  

Term (Tuple) translateCriteriaExpr(strConcat(list[CriteriaExpr] exprs)) {  
  Term trans(Tuple t) {
    return strConcat([translateCriteriaExpr(expr)(t) | CriteriaExpr expr <- exprs]);
  } 
  
  return trans;
}    
  
Relation emptyRel(Heading h) = <h, (), {}>;