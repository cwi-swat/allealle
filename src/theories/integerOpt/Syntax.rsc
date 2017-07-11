module theories::integerOpt::Syntax

extend theories::integer::Syntax;

syntax AlleFormula
  = minimize: "minimize" Expr expr
  | maximize: "maximize" Expr expr
  ;