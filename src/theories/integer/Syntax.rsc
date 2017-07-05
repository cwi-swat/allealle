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
  | minimize:   "minimize" Expr expr
  ; 
  
syntax Expr
  = intLit:         IntLit intLit
  > neg:            "-" Expr e
  > left multiplication: Expr lhs "*" Expr rhs
  | division:       Expr lhs "/" Expr rhs
  | modulo:         Expr lhs "%" Expr rhs
  > left addition:       Expr lhs "+" Expr rhs 
  | left subtraction:    Expr lhs "-" Expr rhs
  > sum:            "sum" "(" Expr expr ")"
  | car:            "#" Expr expr
  ; 

lexical IntLit = [0-9]+;

keyword Keywords = "int" | "sum" | "minimize";