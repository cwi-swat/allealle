module translation::theories::integerOpt::AST

extend translation::AST;

import IO;

data AlleFormula
  = minimize(AlleExpr expr)
  | maximize(AlleExpr expr)
  ;
