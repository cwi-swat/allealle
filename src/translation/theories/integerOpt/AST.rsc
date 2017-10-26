module translation::theories::integerOpt::AST

extend translation::theories::integer::AST;

import IO;

data AlleFormula
  = minimize(AlleExpr expr)
  | maximize(AlleExpr expr)
  ;
