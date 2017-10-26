module translation::theories::integer::Syntax

extend translation::Syntax;

syntax Domain = \int: "int";

syntax Literal 
  = posInt: IntLit lit
  | negInt: "-" IntLit lit
  ;

syntax AlleFormula
  = lt:         AlleExpr lhs "\<"  AlleExpr rhs
  | lte:        AlleExpr lhs "\<=" AlleExpr rhs
  | gt:         AlleExpr lhs "\>"  AlleExpr rhs
  | gte:        AlleExpr lhs "\>=" AlleExpr rhs
  | intEqual:   AlleExpr lhs "="   AlleExpr rhs
  | intInequal: AlleExpr lhs "!="  AlleExpr rhs
  | distinct:   "distinct" "(" AlleExpr expr ")"
  ;
  
syntax AlleExpr
  = variable:             Variable v
  > intLit:               IntLit intLit
  > attributeLookup:      AlleExpr expr "::" AttributeName name
  > neg:                  "-" AlleExpr e
  | abs:                  "|" AlleExpr e "|"
  > left multiplication:  AlleExpr lhs "*" AlleExpr rhs
  | division:             AlleExpr lhs "/" AlleExpr rhs
  | modulo:               AlleExpr lhs "%" AlleExpr rhs
  > left addition:        AlleExpr lhs "+" AlleExpr rhs 
  | left subtraction:     AlleExpr lhs "-" AlleExpr rhs
  > sum:                  "sum" "(" AlleExpr expr ")"
  | car:                  "#" AlleExpr expr
  ; 

lexical IntLit = [0-9]+;

keyword Keywords = "int" | "sum" | "distinct";