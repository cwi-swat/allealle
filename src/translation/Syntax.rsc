module translation::Syntax

extend translation::Layout;

start syntax Problem = problem: Relation* relations AlleFormula* constraints;

syntax Relation 
  = relation:                 Variable v "(" Arity arityOfIds ")" RelationalBound bounds
  | relationWithAttributes:  Variable v "(" Arity arityOfIds "::"  {AttributeHeader ","}+ header ")" RelationalBound bounds
  ;

syntax AttributeHeader
  = header: AttributeName name ":" Domain dom
  ;

syntax RelationalBound
  = exact: "=" "{" {Tuple ","}*tuples "}"
  | atMost: "\<=" "{" {Tuple ","}+ upper "}"
  | atLeastAtMost: "\>=" "{" {Tuple ","}+ lower "}" "\<=" "{" {Tuple ","}+ upper "}"
  ;

syntax Tuple 
  = tup: "\<" {Value ","}+ values "\>"
  | range: "\<" {RangedValue ","}+ from "\>" ".." "\<" {RangedValue ","}+ to "\>"
  ;  

syntax Value
  = id: Id id
  | lit: Literal lit
  | hole: "?"
  ;

syntax RangedValue
  = id: RangedId prefix RangedNr numm
  | idOnly: RangedId id
  | templateLit: Literal lit
  | templateHole: "?"
  ;

syntax Domain = id: "id";  
syntax Literal = none: "none"; 
  
syntax AlleFormula
  = bracket "(" AlleFormula form ")"
  > negation:           "not" AlleFormula form
  > empty:              "no" AlleExpr expr
  | atMostOne:          "lone" AlleExpr expr
  | exactlyOne:         "one" AlleExpr expr
  | nonEmpty:           "some" AlleExpr expr
  | subset:             AlleExpr lhsExpr "in" AlleExpr rhsExpr
  | equal:              AlleExpr lhsExpr "==" AlleExpr rhsExpr
  | inequal:            AlleExpr lhsExpr "!==" AlleExpr rhsExpr
  > left conjunction:   AlleFormula lhsForm "&&" AlleFormula rhsForm
  | left disjunction:   AlleFormula lhsForm "||" AlleFormula rhsForm  
  > implication:        AlleFormula lhsForm "=\>" AlleFormula rhsForm
  | equality:           AlleFormula lhsForm "\<=\>" AlleFormula rhsForm
  > let:                "let" {VarDeclaration ","}+ decls "|" AlleFormula form
  > universal:          "forall" {VarDeclaration ","}+ decls "|" AlleFormula form
  | existential:        "exists" {VarDeclaration ","}+ decls "|" AlleFormula form 
  ; 

syntax VarDeclaration = varDecl: Variable var ":" AlleExpr expr;

syntax AlleExpr
  = bracket "(" AlleExpr expr ")"
  > variable:           Variable v
  > right \join:         AlleExpr lhs "." AlleExpr rhs
  > transpose:          "~" AlleExpr expr
  | closure:            "^" AlleExpr expr
  | reflexClosure:      "*" AlleExpr expr
  > attributeLookup:    AlleExpr expr "::" AttributeName name
  | left union:         AlleExpr lhs "++" AlleExpr rhs 
  | left override:      AlleExpr lhs "+++" AlleExpr rhs
  | left intersection:  AlleExpr lhs "&" AlleExpr rhs
  | left difference:    AlleExpr lhs "\\" AlleExpr rhs
  | left product:       AlleExpr lhs "-\>" AlleExpr rhs
  | ifThenElse:         AlleFormula form "?" AlleExpr then ":" AlleExpr else
  | comprehension:      "{" {VarDeclaration ","}+ decls "|" AlleFormula form "}"
  ;

lexical RangedId = ([a-z_] !<< [a-z_][a-zA-Z_]* !>> [a-zA-Z_]) \ Keywords;
lexical RangedNr = [0-9]+;

lexical Id = ([a-z_] !<< [a-z_][a-zA-Z0-9_]* !>> [a-zA-Z0-9_]) \ Keywords;
lexical AttributeName = ([a-zA-Z_] !<< [a-zA-Z_][a-zA-Z0-9_\']* !>> [a-zA-Z0-9_]) \ Keywords;
lexical Arity = [0-9]+;

lexical Variable = ([a-zA-Z_] !<< [a-zA-Z_][a-zA-Z0-9_\']* !>> [a-zA-Z0-9_]) \ Keywords;

keyword Keywords = "none";
keyword Keywords = "no" | "lone" | "one" | "some" | "not" | "forall" | "exists" | "let";
