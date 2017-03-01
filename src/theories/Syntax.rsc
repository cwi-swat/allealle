module theories::Syntax

extend theories::Layout;

start syntax Problem = problem: Universe uni RelationalBound* bounds AlleFormula* constraints;

syntax Universe = universe: "{" {Atom ","}+ atoms "}";

syntax RelationalBound 
  = relationalBound: Variable v ":" Arity a "[" "{" {Tuple ","}* lower "}" "," "{" {Tuple ","}* upper "}" "]"
  | relationalBoundWithTheory: Variable v "(" Theory theory ")" ":" Arity a "[" "{" {Tuple ","}* lower "}" "," "{" {Tuple ","}* upper "}" "]"
  ;
  
syntax Theory = none: "none";  
  
syntax Tuple = \tuple: "\<" {Atom ","}+ atoms "\>"; 
  
syntax AlleFormula
  = bracket "(" AlleFormula form ")"
  ; 

syntax Expr
  = bracket "(" Expr expr ")"
  ;

lexical Atom = ([a-z] !<< [a-z][a-z A-Z 0-9]* !>> [a-z A-Z 0-9]) \ Keywords;

lexical Variable = ([a-z A-Z] !<< [a-z A-Z][a-z A-Z 0-9]* !>> [a-z A-Z 0-9]) \ Keywords;

lexical Arity = [0-9]+;

keyword Keywords = "none";