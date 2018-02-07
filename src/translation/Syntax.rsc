module translation::Syntax

extend translation::Layout;

start syntax Problem = problem: Relation* relations AlleFormula* constraints;

syntax Relation 
  = RelVar v "(" {HeaderAttribute ","}+ header ")" RelationalBound bounds
  ;

syntax HeaderAttribute
  = AttributeName name ":" Domain dom
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
  = Idd id
  | lit: Literal lit
  | "?"
  ;

syntax RangedValue
  = id: RangedId prefix RangedNr numm
  | idOnly: RangedId id
  | templateLit: Literal lit
  | "?"
  ;

syntax Domain 
  = "id"
  ;  
  
syntax Literal 
  = idLit: "\'" Idd id "\'" 
  ; 
  
syntax AlleFormula
  = bracket "(" AlleFormula form ")"
  > \filter:            AlleExpr expr "::" "[" Criteria criteria "]"
  > negation:           ("not"|"¬") AlleFormula form
  > empty:              "no" AlleExpr expr
  | atMostOne:          "lone" AlleExpr expr
  | exactlyOne:         "one" AlleExpr expr
  | nonEmpty:           "some" AlleExpr expr
  | subset:             AlleExpr lhsExpr ("in" | "⊆") AlleExpr rhsExpr
  | equal:              AlleExpr lhsExpr "=" AlleExpr rhsExpr
  | inequal:            AlleExpr lhsExpr ("!=" | "≠") AlleExpr rhsExpr
  > left conjunction:   AlleFormula lhsForm ("&&" | "∧") AlleFormula rhsForm
  | left disjunction:   AlleFormula lhsForm ("||" | "∨") AlleFormula rhsForm  
  > implication:        AlleFormula lhsForm ("=\>" | "⇒") AlleFormula rhsForm
  | equality:           AlleFormula lhsForm ("\<=\>" | "⇔") AlleFormula rhsForm
  > let:                "let" {VarBinding ","}+ bindings "|" AlleFormula form
  > universal:          ("forall" | "∀") {VarDeclaration ","}+ decls "|" AlleFormula form
  | existential:        ("exists" | "∃") {VarDeclaration ","}+ decls "|" AlleFormula form 
  ; 

syntax VarDeclaration = varDecl: RelVar var (":" | "∈") AlleExpr expr;

syntax VarBinding = varBinding: RelVar var "=" AlleExpr expr;

syntax AlleExpr
  = bracket "(" AlleExpr expr ")"
  > variable:           RelVar v
  | lit:                Literal l
  > rename:             AlleExpr r "[" {Rename ","}+ "]"
  | project:            AlleExpr r "[" {AttributeName ","}+ "]"
  | select:             AlleExpr r "where" Criteria criteria
  > transpose:          "~" TupleAttributeSelection tas AlleExpr r
  | closure:            "^" TupleAttributeSelection tas AlleExpr r
  | reflexClosure:      "*" TupleAttributeSelection tas AlleExpr r
  > left naturalJoin:   AlleExpr lhs ("|x|" | "⨝") AlleExpr rhs
  | left dotJoin:       AlleExpr lhs "."   AlleExpr rhs
  > left (union:        AlleExpr lhs ("+" | "∪")   AlleExpr rhs
         |intersection: AlleExpr lhs ("&" | "∩")  AlleExpr rhs
         |difference:   AlleExpr lhs ("-" | "∖")   AlleExpr rhs
         |product:      AlleExpr lhs ("x" | "⨯")   AlleExpr rhs
         )
  //| comprehension:     "{" {VarDeclaration ","}+ decls "|" AlleFormula form "}"
  //| ifThenElse:         AlleFormula form "?" AlleExpr then ":" AlleExpr else
  ;

syntax TupleAttributeSelection 
  = "\<" AttributeName first "," AttributeName second "\>"
  ;

syntax Rename = AttributeName new "/" AttributeName orig;

syntax Criteria
  = bracket "(" Criteria ")"
  > "not" Criteria
  > left CriteriaExpr lhs "=" CriteriaExpr rhs
  | left CriteriaExpr lhs "!=" CriteriaExpr rhs
  > left ( Criteria lhs "&&" Criteria rhs
         | Criteria lhs "||" Criteria rhs
         )
  ;

syntax CriteriaExpr
  = AttributeName att
  | Literal l
  ;

lexical RangedId = ([a-z_] !<< [a-z_][a-zA-Z_]* !>> [a-zA-Z_]) \ Keywords;
lexical RangedNr = [0-9]+;

lexical Idd = ([a-z_] !<< [a-z_][a-zA-Z0-9_]* !>> [a-zA-Z0-9_]) \ Keywords;

lexical Id = ([a-z_] !<< [a-z][a-zA-Z0-9_]* !>> [a-zA-Z0-9_]) \ Keywords;
lexical AttributeName = ([a-zA-Z] !<< [a-zA-Z][a-zA-Z0-9_\']* !>> [a-zA-Z0-9_]) \ Keywords;
lexical Arity = [0-9]+;

lexical RelVar = ([a-zA-Z] !<< [a-zA-Z_][a-zA-Z0-9_\']* !>> [a-zA-Z0-9_]) \ Keywords;

keyword Keywords = "none" | "|x|" | "where";
keyword Keywords = "no" | "lone" | "one" | "some" | "not" | "forall" | "exists" | "let";
