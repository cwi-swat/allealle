module extended::Syntax

extend orig::Syntax;

syntax RelationalBound = relationalBound: Variable v  "(" Sort sort ")" ":" Arity a "[" "{" {Tuple ","}* lower "}" "," "{" {Tuple ","}* upper "}" "]";

// Integer theory extensions
syntax Sort
	= intSort: "int"
	;

syntax Formula
	= lt:		Expr lhs "\<" Expr rhs
	| lte:		Expr lhs "\<=" Expr rhs
	| gt:		Expr lhs "\>" Expr rhs
	| gte:		Expr lhs "\>=" Expr rhs
	| intEqual: Expr lhs "=" Expr rhs
	;	
	
syntax Expr
	= intLit:			IntLit intLit
	//| intProjection:	"[" Expr expr "]"
	| multiplication:	Expr lhs "*" Expr rhs
	| division:			Expr lhs "\\" Expr rhs
	> addition:			Expr lhs "+" Expr rhs
	| subtraction:		Expr lhs "-" Expr rhs
	;

lexical IntLit = [0-9]+;