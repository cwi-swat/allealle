module orig::Syntax

extend lang::std::Layout;

start syntax Problem = problem: Universe uni RelationalBound* bounds Formula* formulas;

syntax Universe = universe: "{" {Atom ","}+ atoms "}";

syntax RelationalBound = relationalBound: Variable v ":" Arity a "[" "{" {Tuple ","}* lower "}" "," "{" {Tuple ","}* upper "}" "]";
syntax Tuple = \tuple: "\<" {Atom ","}+ atoms "\>";	
  
syntax Formula
	= bracket "(" Formula form ")"
	| universal:	"forall" {VarDeclaration ","}+ decls "|" Formula form
	| existential:	"exists" {VarDeclaration ","}+ decls "|" Formula form 
	> implication:	Formula lhsForm "=\>" Formula rhsForm
	| equality:		Formula lhsForm "\<=\>" Formula rhsForm
	> empty:		"no" Expr expr
	| atMostOne:	"lone" Expr expr
	| exactlyOne:	"one" Expr expr
	| nonEmpty:		"some" Expr expr
	| subset:		Expr lhsExpr "in" Expr rhsExpr
	| equal:		Expr lhsExpr "==" Expr rhsExpr
	| conjunction:	Formula lhsForm "&&" Formula rhsForm
	| disjunction:	Formula lhsForm "||" Formula rhsForm
	> negation:		"not" Formula form
	; 

syntax Expr
	= bracket "(" Expr expr ")"
	> \join:		Expr lhs "." Expr rhs
	> variable:		Variable v
	| transpose:	"~" Expr expr
	| closure:		"^" Expr expr
	| reflexClosure:"*" Expr expr
	| union:		Expr lhs "++" Expr rhs 
	| intersection:	Expr lhs "&" Expr rhs
	| difference:	Expr lhs "--" Expr rhs
	| product:		Expr lhs "-\>" Expr rhs
	| ifThenElse:	Formula form "?" Expr then ":" Expr else
	| comprehension:"{" {VarDeclaration ","}+ decls "|" Formula form "}"
	;

syntax VarDeclaration = varDecl: Variable var ":" Expr expr;

lexical Atom = ([a-z] !<< [a-z][a-z A-Z 0-9]* !>> [a-z A-Z 0-9]) \ Keywords;
lexical Variable = ([a-z A-Z] !<< [a-z A-Z][a-z A-Z 0-9]* !>> [a-z A-Z 0-9]) \ Keywords;
lexical Arity = [0-9]+;

keyword Keywords = "no" | "lone" | "one" | "some" | "not" | "forall" | "exists";