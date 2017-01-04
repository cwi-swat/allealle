module relational::Syntax

extend Syntax;
  
syntax Theory =   relational: "rel";  

syntax Formula
	= universal:	  "forall" {VarDeclaration ","}+ decls "|" Formula form
	| existential:	"exists" {VarDeclaration ","}+ decls "|" Formula form 
	> implication:	Formula lhsForm "=\>" Formula rhsForm
	| equality:		  Formula lhsForm "\<=\>" Formula rhsForm
	> empty:		    "no" Expr expr
	| atMostOne:	  "lone" Expr expr
	| exactlyOne:	  "one" Expr expr
	| nonEmpty:		  "some" Expr expr
	| subset:		    Expr lhsExpr "in" Expr rhsExpr
	| equal:		    Expr lhsExpr "==" Expr rhsExpr
	| conjunction:	Formula lhsForm "&&" Formula rhsForm
	| disjunction:	Formula lhsForm "||" Formula rhsForm
	> negation:		  "not" Formula form
	; 

syntax Expr
	= \join:		     Expr lhs "." Expr rhs
	| accessorJoin:  Expr col "[" Expr select "]"
	> variable:		   Variable v
	| transpose:	   "~" Expr expr
	| closure:		   "^" Expr expr
	| reflexClosure: "*" Expr expr
	| union:		     Expr lhs "++" Expr rhs 
	| intersection:	 Expr lhs "&" Expr rhs
	| difference:	   Expr lhs "\\" Expr rhs
	| left product:	 Expr lhs "-\>" Expr rhs
	| ifThenElse:	   Formula form "?" Expr then ":" Expr else
	| comprehension: "{" {VarDeclaration ","}+ decls "|" Formula form "}"
	;

syntax VarDeclaration = varDecl: Variable var ":" Expr expr;

keyword Keywords = "no" | "lone" | "one" | "some" | "not" | "forall" | "exists";