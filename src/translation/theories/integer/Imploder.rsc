module translation::theories::integer::Imploder

import translation::Imploder;

import translation::theories::integer::Syntax;
import translation::theories::integer::AST;
import translation::DomainResolver;
import translation::theories::integer::DomainResolver;

import ParseTree;
import String;

translation::AST::Domain implode((Domain)`int`, ResolvedDomains dom) = \int();  

translation::AST::Literal implode((Literal)`<IntLit i>`, ResolvedDomains dom) = posInt(toInt("<i>"));  
translation::AST::Literal implode((Literal)`-<IntLit i>`, ResolvedDomains dom) = negInt(toInt("<i>"));  
 
translation::AST::AlleFormula implode((AlleFormula)`<AlleExpr lhs> \< <AlleExpr rhs>`, ResolvedDomains dom)
  = lt(implode(lhs,dom),implode(rhs,dom))
  when dom[lhs@\loc] == integer(),
       dom[rhs@\loc] == integer();

translation::AST::AlleFormula implode((AlleFormula)`<AlleExpr lhs> \<= <AlleExpr rhs>`, ResolvedDomains dom)
  = lte(implode(lhs,dom),implode(rhs,dom))
  when dom[lhs@\loc] == integer(),
       dom[rhs@\loc] == integer();

translation::AST::AlleFormula implode((AlleFormula)`<AlleExpr lhs> \> <AlleExpr rhs>`, ResolvedDomains dom)
  = gt(implode(lhs,dom),implode(rhs,dom))
  when dom[lhs@\loc] == integer(),
       dom[rhs@\loc] == integer();

translation::AST::AlleFormula implode((AlleFormula)`<AlleExpr lhs> \>= <AlleExpr rhs>`, ResolvedDomains dom)
  = gte(implode(lhs,dom),implode(rhs,dom))
  when dom[lhs@\loc] == integer(),
       dom[rhs@\loc] == integer();

translation::AST::AlleFormula implode((AlleFormula)`<AlleExpr lhs> = <AlleExpr rhs>`, ResolvedDomains dom)
  = intEqual(implode(lhs,dom),implode(rhs,dom))
  when dom[lhs@\loc] == integer(),
       dom[rhs@\loc] == integer();

translation::AST::AlleFormula implode((AlleFormula)`<AlleExpr lhs> != <AlleExpr rhs>`, ResolvedDomains dom)
  = intInequal(implode(lhs,dom),implode(rhs,dom))
  when dom[lhs@\loc] == integer(),
       dom[rhs@\loc] == integer();

translation::AST::AlleFormula implode((AlleFormula)`distinct (<AlleExpr expr>)`, ResolvedDomains dom)
  = distinct(implode(expr,dom))
  when dom[expr@\loc] == integer();

translation::AST::AlleExpr implode((AlleExpr)`<IntLit i>`, ResolvedDomains dom)
  = intLit(toInt("<i>"));

translation::AST::AlleExpr implode((AlleExpr)`- <AlleExpr expr>`, ResolvedDomains dom)
  = neg(implode(expr,dom))
  when dom[expr@\loc] == integer();

translation::AST::AlleExpr implode((AlleExpr)`|<AlleExpr expr>|`, ResolvedDomains dom)
  = abs(implode(expr,dom))
  when dom[expr@\loc] == integer();

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> * <AlleExpr rhs>`, ResolvedDomains dom)
  = multiplication(implode(lhs,dom),implode(rhs,dom))
  when dom[lhs@\loc] == integer(), 
       dom[rhs@\loc] == integer();

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> / <AlleExpr rhs>`, ResolvedDomains dom)
  = division(implode(lhs,dom),implode(rhs,dom))
  when dom[lhs@\loc] == integer(),
       dom[rhs@\loc] == integer(); 

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> % <AlleExpr rhs>`, ResolvedDomains dom)
  = modulo(implode(lhs,dom),implode(rhs,dom))
  when dom[lhs@\loc] == integer(),
       dom[rhs@\loc] == integer(); 

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> + <AlleExpr rhs>`, ResolvedDomains dom)
  = addition(implode(lhs,dom),implode(rhs,dom))
  when dom[lhs@\loc] == integer(),
       dom[rhs@\loc] == integer(); 

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> - <AlleExpr rhs>`, ResolvedDomains dom)
  = subtraction(implode(lhs,dom),implode(rhs,dom))
  when dom[lhs@\loc] == integer(),
       dom[rhs@\loc] == integer(); 

translation::AST::AlleExpr implode((AlleExpr)`sum(<AlleExpr expr>)`, ResolvedDomains dom)
  = sum(implode(expr,dom))
  when dom[expr@\loc] == integer(); 

translation::AST::AlleExpr implode((AlleExpr)`#<AlleExpr expr>`, ResolvedDomains dom)
  = car(implode(expr,dom)); 
       