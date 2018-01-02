module translation::theories::integer::Syntax

extend translation::Syntax;

syntax Domain = "int";

syntax Literal 
  = IntLit i
  ;
  
syntax AlleExpr
  = neg:                  "-" AlleExpr
  > sum:                  "sum" "(" AlleExpr expr ")"
  | car:                  "#" AlleExpr expr
  ; 

syntax Restriction
  = distinct:   "distinct" RestrictionExpr expr
  > left lt:    RestrictionExpr lhs "\<" RestrictionExpr rhs
  | left lte:   RestrictionExpr lhs "\<=" RestrictionExpr rhs
  | left gt:    RestrictionExpr lhs "\>" RestrictionExpr rhs
  | left gte:   RestrictionExpr lhs "\>=" RestrictionExpr rhs
  ; 

syntax RestrictionExpr
  = abs:        "|" RestrictionExpr expr "|"
  > left mult:  RestrictionExpr lhs "*" RestrictionExpr rhs
  | div:        RestrictionExpr lhs "/" RestrictionExpr rhs
  | \mod:       RestrictionExpr lhs "%" RestrictionExpr rhs
  > left add:   RestrictionExpr "+" RestrictionExpr rhs 
  | left sub:   RestrictionExpr "-" RestrictionExpr rhs
  ;
  
lexical IntLit = [0-9]+;

keyword Keywords = "int" | "sum" | "distinct";