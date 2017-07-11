module theories::Syntax

extend theories::Layout;

start syntax Problem = problem: Universe uni RelationalBound* bounds AlleFormula* constraints;

syntax Universe = universe: "{" {AtomDecl ","}+ atoms "}";

syntax AtomDecl 
  = atomOnly:           Atom atom
  | atomAndTheory:      Atom atom "(" Theory theory ")"
  | atomTheoryAndValue: Atom atom "(" Theory theory ")" "=" AtomValue val
  ;

syntax AtomValue = none: "none"; 

syntax RelationalBound 
  = relationalBound: Variable v ":" Arity a "[" "{" {Tuple ","}* lower "}" "," "{" {Tuple ","}* upper "}" "]"
  ;
  
syntax Theory = none: "none";  
  
syntax Tuple = \tuple: "\<" {Atom ","}+ atoms "\>"; 
  
syntax VarDeclaration = varDecl: Variable var ":" Expr expr;

syntax AlleFormula
  = bracket "(" AlleFormula form ")"
  > negation:     "not" AlleFormula form
  > empty:        "no" Expr expr
  | atMostOne:    "lone" Expr expr
  | exactlyOne:   "one" Expr expr
  | nonEmpty:     "some" Expr expr
  | subset:       Expr lhsExpr "in" Expr rhsExpr
  | equal:        Expr lhsExpr "==" Expr rhsExpr
  | inequal:      Expr lhsExpr "!==" Expr rhsExpr
  > left conjunction:  AlleFormula lhsForm "&&" AlleFormula rhsForm
  | left disjunction:  AlleFormula lhsForm "||" AlleFormula rhsForm  
  > implication:  AlleFormula lhsForm "=\>" AlleFormula rhsForm
  | equality:     AlleFormula lhsForm "\<=\>" AlleFormula rhsForm
  > universal:    "forall" {VarDeclaration ","}+ decls "|" AlleFormula form
  | existential:  "exists" {VarDeclaration ","}+ decls "|" AlleFormula form 
  ; 

syntax Expr
  = bracket "(" Expr expr ")"
  > \join:              Expr lhs "." Expr rhs
  | accessorJoin:       Expr col "[" Expr select "]"
  > variable:           Variable v
  | transpose:          "~" Expr expr
  | closure:            "^" Expr expr
  | reflexClosure:      "*" Expr expr
  | left union:         Expr lhs "++" Expr rhs 
  | left intersection:  Expr lhs "&" Expr rhs
  | left difference:    Expr lhs "\\" Expr rhs
  | left product:       Expr lhs "-\>" Expr rhs
  | ifThenElse:         AlleFormula form "?" Expr then ":" Expr else
  | comprehension:      "{" {VarDeclaration ","}+ decls "|" AlleFormula form "}"
  ;

lexical Atom = ([a-z_] !<< [a-z_][a-zA-Z0-9_]* !>> [a-zA-Z0-9_]) \ Keywords;

lexical Variable = ([a-zA-Z_] !<< [a-zA-Z_][a-zA-Z0-9_\']* !>> [a-zA-Z0-9_]) \ Keywords;

lexical Arity = [0-9]+;

keyword Keywords = "none";
keyword Keywords = "no" | "lone" | "one" | "some" | "not" | "forall" | "exists";
