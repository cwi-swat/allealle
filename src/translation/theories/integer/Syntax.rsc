module translation::theories::integer::Syntax

syntax Domain = "int";

syntax Criteria
  = non-assoc  (lt:    CriteriaExpr lhsExpr "\<" CriteriaExpr rhsExpr
              | lte:   CriteriaExpr lhsExpr "\<=" CriteriaExpr rhsExpr
              | gt:    CriteriaExpr lhsExpr "\>" CriteriaExpr rhsExpr
              | gte:   CriteriaExpr lhsExpr "\>=" CriteriaExpr rhsExpr
              )
  ; 

syntax CriteriaExpr
  = abs:              "|" CriteriaExpr expr "|"
  | neg:               "-" CriteriaExpr expr
  //| non-assoc exp:     CriteriaExpr lhs "^" CriteriaExpr rhs 
  > left mult:         CriteriaExpr lhs "*" CriteriaExpr rhs
  | non-assoc ( div:   CriteriaExpr lhs "/" CriteriaExpr rhs
              | \mod:  CriteriaExpr lhs "%" CriteriaExpr rhs
              )
  > left ( add:        CriteriaExpr "+" CriteriaExpr rhs 
         | sub:        CriteriaExpr "-" CriteriaExpr rhs
         )
  > non-assoc ( "min" "(" CriteriaExpr a "," CriteriaExpr b ")"
              | "max" "(" CriteriaExpr a "," CriteriaExpr b ")"
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

keyword Keywords = "int";