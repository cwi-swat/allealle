module translation::theories::integer::Syntax

extend translation::Syntax;

syntax Domain = "int";

syntax Criteria
  = non-assoc  (lt:    CriteriaExpr lhs "\<" CriteriaExpr rhs
              | lte:   CriteriaExpr lhs "\<=" CriteriaExpr rhs
              | gt:    CriteriaExpr lhs "\>" CriteriaExpr rhs
              | gte:   CriteriaExpr lhs "\>=" CriteriaExpr rhs
              )
  ; 

syntax CriteriaExpr
  = abs:              "|" CriteriaExpr expr "|"
  | neg:               "-" CriteriaExpr expr
  > left mult:         CriteriaExpr lhs "*" CriteriaExpr rhs
  | non-assoc ( div:   CriteriaExpr lhs "/" CriteriaExpr rhs
              | \mod:  CriteriaExpr lhs "%" CriteriaExpr rhs
              )
  > left ( add:        CriteriaExpr "+" CriteriaExpr rhs 
         | sub:        CriteriaExpr "-" CriteriaExpr rhs
         )
  ;
 
syntax Literal 
  = intLit: IntLit i
  ; 

syntax AggregateFunction 
  = car: "count" "()"
  | sum: "sum" "(" AttributeName att ")"
  | min: "min" "(" AttributeName att ")"
  | max: "max" "(" AttributeName att ")"
  | avg: "avg" "(" AttributeName att ")"
  ;  
  
lexical IntLit = [0-9]+;

keyword Keywords = "int" | "sum" | "distinct";