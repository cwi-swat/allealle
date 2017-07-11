module theories::integerOpt::AST

extend theories::integer::AST;

import IO;

data AlleFormula
  = minimize(Expr expr)
  | maximize(Expr expr)
  ;
