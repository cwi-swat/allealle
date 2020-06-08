module translation::theories::string::Imploder

import translation::Syntax;
import translation::theories::string::AST; 

import ParseTree;

translation::AST::Domain implode((Domain)`str`) = strDom();  

translation::AST::AlleLiteral implode((Literal)`<StrLit s>`) = strLit("<s>");  

translation::AST::CriteriaExpr implode((CriteriaExpr)`length(<CriteriaExpr expr>)`) = strLength(implode(expr));
translation::AST::CriteriaExpr implode((CriteriaExpr)`toInt(<CriteriaExpr expr>)`) = strToInt(implode(expr));
translation::AST::CriteriaExpr implode((CriteriaExpr)`toStr(<CriteriaExpr expr>)`) = intToStr(implode(expr));

translation::AST::CriteriaExpr implode((CriteriaExpr)`<CriteriaExpr lhs> ++ <CriteriaExpr rhs>`) = strConcat(implode(lhs), implode(rhs));
translation::AST::CriteriaExpr implode((CriteriaExpr)`substr(<CriteriaExpr expr>, <CriteriaExpr offset>, <CriteriaExpr length>)`) = substr(implode(expr), implode(offset), implode(length));