module translation::theories::integerOpt::Syntax

extend translation::theories::integer::Syntax;

syntax AlleFormula
  = minimize: "minimize" AlleExpr expr
  | maximize: "maximize" AlleExpr expr
  ;
  
keyword Keywords = "minimize" | "maximize";