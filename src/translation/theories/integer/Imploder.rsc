module translation::theories::integer::Imploder

import translation::Syntax;

import translation::theories::integer::AST; 

import ParseTree;
import String;

translation::AST::Domain implode((Domain)`int`) = intDom();  

translation::AST::AlleLiteral implode((Literal)`<IntLit i>`) = intLit(toInt("<i>"));  

translation::AST::AggregateFunction implode((AggregateFunction)`count()`)
  = count();

translation::AST::AggregateFunction implode((AggregateFunction)`sum(<AttributeName att>)`)
  = sum("<att>");

translation::AST::AggregateFunction implode((AggregateFunction)`min(<AttributeName att>)`)
  = min("<att>");

translation::AST::AggregateFunction implode((AggregateFunction)`max(<AttributeName att>)`)
  = max("<att>");

translation::AST::AggregateFunction implode((AggregateFunction)`avg(<AttributeName att>)`)
  = avg("<att>");
 
translation::AST::Criteria implode((Criteria)`<CriteriaExpr lhs> \< <CriteriaExpr rhs>`)
  = lt(implode(lhs),implode(rhs));

translation::AST::Criteria implode((Criteria)`<CriteriaExpr lhs> \<= <CriteriaExpr rhs>`)
  = lte(implode(lhs),implode(rhs));

translation::AST::Criteria implode((Criteria)`<CriteriaExpr lhs> \> <CriteriaExpr rhs>`)
  = gt(implode(lhs),implode(rhs));

translation::AST::Criteria implode((Criteria)`<CriteriaExpr lhs> \>= <CriteriaExpr rhs>`)
  = gte(implode(lhs),implode(rhs));

translation::AST::CriteriaExpr implode((CriteriaExpr)`- <CriteriaExpr expr>`)
  = neg(implode(expr));

translation::AST::CriteriaExpr implode((CriteriaExpr)`|<CriteriaExpr expr>|`)
  = abs(implode(expr));

//translation::AST::CriteriaExpr implode((CriteriaExpr)`<CriteriaExpr base>^<CriteriaExpr expo>`)
//  = exp(implode(base),implode(expo));

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

translation::AST::CriteriaExpr implode((CriteriaExpr)`min(<CriteriaExpr a>,<CriteriaExpr b>)`)
  = min(implode(a),implode(b));
  
translation::AST::CriteriaExpr implode((CriteriaExpr)`max(<CriteriaExpr a>,<CriteriaExpr b>)`)
  = max(implode(a),implode(b));
  