module theories::integer::Syntax

extend theories::Syntax;

syntax Theory = intTheory: "int";

syntax AtomValue 
  = intExpr: Expr expr
  ;

syntax AlleFormula
  = lt:         Expr lhs "\<"  Expr rhs
  | lte:        Expr lhs "\<=" Expr rhs
  | gt:         Expr lhs "\>"  Expr rhs
  | gte:        Expr lhs "\>=" Expr rhs
  | intEqual:   Expr lhs "="   Expr rhs
  | intInequal: Expr lhs "!="  Expr rhs
  ; 
  
syntax Expr
  = intLit:         IntLit intLit
  > multiplication: Expr lhs "*" Expr rhs
  | division:       Expr lhs "/" Expr rhs
  | modulo:         Expr lhs "%" Expr rhs
  > addition:       Expr lhs "+" Expr rhs 
  | subtraction:    Expr lhs "-" Expr rhs
  > sum:            "sum" "(" {VarDeclaration ","}+ decls "|" Expr expr ")"
  ; 

lexical IntLit = [0-9]+;

keyword Keywords = "int" | "sum";