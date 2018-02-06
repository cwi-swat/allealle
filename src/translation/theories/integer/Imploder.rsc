module translation::theories::integer::Imploder

import translation::Imploder;

import translation::theories::integer::Syntax;
import translation::theories::integer::AST;

import ParseTree;
import String;

translation::AST::Domain implode((Domain)`int`) = intDom();  

translation::AST::AlleLiteral implode((Literal)`<IntLit i>`) = intLit(toInt("<i>"));  
 
translation::AST::Criteria implode((Criteria)`<CriteriaExpr lhs> \< <CriteriaExpr rhs>`)
  = lt(implode(lhs),implode(rhs));

translation::AST::Criteria implode((Criteria)`<CriteriaExpr lhs> \<= <CriteriaExpr rhs>`)
  = lte(implode(lhs),implode(rhs));

translation::AST::Criteria implode((Criteria)`<CriteriaExpr lhs> \> <CriteriaExpr rhs>`)
  = gt(implode(lhs),implode(rhs));

translation::AST::Criteria implode((Criteria)`<CriteriaExpr lhs> \>= <CriteriaExpr rhs>`)
  = gte(implode(lhs),implode(rhs));

translation::AST::AlleLiteral implode((Literal)`<IntLit i>`)
  = intLit(toInt("<i>"));

translation::AST::CriteriaExpr implode((CriteriaExpr)`( <CriteriaExpr expr> )`)
  = implode(expr);
  
translation::AST::CriteriaExpr implode((CriteriaExpr)`- <CriteriaExpr expr>`)
  = neg(implode(expr));

translation::AST::CriteriaExpr implode((CriteriaExpr)`|<CriteriaExpr expr>|`)
  = abs(implode(expr));

translation::AST::CriteriaExpr implode((CriteriaExpr)`<CriteriaExpr lhs> * <CriteriaExpr rhs>`)
  = multiplication(implode(lhs),implode(rhs));

translation::AST::CriteriaExpr implode((CriteriaExpr)`<CriteriaExpr lhs> / <CriteriaExpr rhs>`)
  = division(implode(lhs),implode(rhs)); 

translation::AST::CriteriaExpr implode((CriteriaExpr)`<CriteriaExpr lhs> % <CriteriaExpr rhs>`)
  = modulo(implode(lhs),implode(rhs));

translation::AST::CriteriaExpr implode((CriteriaExpr)`<CriteriaExpr lhs> + <CriteriaExpr rhs>`)
  = addition(implode(lhs),implode(rhs)); 

translation::AST::CriteriaExpr implode((CriteriaExpr)`<CriteriaExpr lhs> - <CriteriaExpr rhs>`)
  = subtraction(implode(lhs),implode(rhs));
