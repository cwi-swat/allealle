module translation::theories::integer::Syntax

extend translation::Syntax;

syntax Domain = "int";

syntax Criteria
  = left lt:    CriteriaExpr lhs "\<" CriteriaExpr rhs
  | left lte:   CriteriaExpr lhs "\<=" CriteriaExpr rhs
  | left gt:    CriteriaExpr lhs "\>" CriteriaExpr rhs
  | left gte:   CriteriaExpr lhs "\>=" CriteriaExpr rhs
  ; 

syntax CriteriaExpr
  = "(" CriteriaExpr expr ")"
  > abs:        "|" CriteriaExpr expr "|"
  | neg:        "-" CriteriaExpr expr
  > left mult:  CriteriaExpr lhs "*" CriteriaExpr rhs
  | div:        CriteriaExpr lhs "/" CriteriaExpr rhs
  | \mod:       CriteriaExpr lhs "%" CriteriaExpr rhs
  > left add:   CriteriaExpr "+" CriteriaExpr rhs 
  | left sub:   CriteriaExpr "-" CriteriaExpr rhs
  ;
 
syntax Literal 
  = intLit: IntLit i
  ; 
  
lexical IntLit = [0-9]+;

keyword Keywords = "int" | "sum" | "distinct";