module theories::integer::Syntax

extend theories::Syntax;

syntax Theory = intTheory: "int";

syntax Value 
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
  = variable:           Variable v
  | attributeLookup:    Expr expr "::" Variable name
  > intLit:         IntLit intLit
  > neg:            "-" Expr e
  > left multiplication: Expr lhs "*" Expr rhs
  | division:       Expr lhs "/" Expr rhs
  | modulo:         Expr lhs "%" Expr rhs
  > left addition:       Expr lhs "+" Expr rhs 
  | left subtraction:    Expr lhs "-" Expr rhs
  > sum:            "sum" "(" Expr expr ")"
  | sumBind:        "sum" "(" Expr bind "," Expr expr ")"
  | car:            "#" Expr expr
  | carBind:        "#" "(" Expr bind "," Expr expr ")"
  ; 

lexical IntLit = [0-9]+;

keyword Keywords = "int" | "sum" | "minimize";