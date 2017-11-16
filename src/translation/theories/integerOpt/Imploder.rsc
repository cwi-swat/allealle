module translation::theories::integerOpt::Imploder

import translation::Imploder;
import translation::theories::integerOpt::Syntax;
import translation::theories::integerOpt::AST;

import translation::DomainResolver;
import translation::theories::integer::DomainResolver;

import ParseTree;
import String;
 
translation::AST::AlleFormula implode((AlleFormula)`minimize <AlleExpr expr>`, ResolvedDomains dom)
  = minimize(implode(expr,dom))
  when dom[expr@\loc] == integer();

translation::AST::AlleFormula implode((AlleFormula)`maximize <AlleExpr expr>`, ResolvedDomains dom)
  = maximize(implode(expr,dom))
  when dom[expr@\loc] == integer();
  