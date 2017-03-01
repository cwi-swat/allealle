module theories::relational::Syntax

extend theories::Syntax;
  
syntax Theory =   relational: "rel";  

syntax AlleFormula
	= universal:	  "forall" {VarDeclaration ","}+ decls "|" AlleFormula form
	| existential:	"exists" {VarDeclaration ","}+ decls "|" AlleFormula form 
	> implication:	AlleFormula lhsForm "=\>" AlleFormula rhsForm
	| equality:		  AlleFormula lhsForm "\<=\>" AlleFormula rhsForm
  > left conjunction:  AlleFormula lhsForm "&&" AlleFormula rhsForm
  | left disjunction:  AlleFormula lhsForm "||" AlleFormula rhsForm  
	> empty:		    "no" Expr expr
	| atMostOne:	  "lone" Expr expr
	| exactlyOne:	  "one" Expr expr
	| nonEmpty:		  "some" Expr expr
	| subset:		    Expr lhsExpr "in" Expr rhsExpr
	| equal:		    Expr lhsExpr "==" Expr rhsExpr
	> negation:		  "not" AlleFormula form
	; 

syntax Expr
	= \join:		     Expr lhs "." Expr rhs
	| accessorJoin:  Expr col "[" Expr select "]"
	> variable:		   Variable v
	| transpose:	   "~" Expr expr
	| closure:		   "^" Expr expr
	| reflexClosure: "*" Expr expr
	| left union:		     Expr lhs "++" Expr rhs 
	| left intersection:	 Expr lhs "&" Expr rhs
	| left difference:	   Expr lhs "\\" Expr rhs
	| left product:	 Expr lhs "-\>" Expr rhs
	| ifThenElse:	   AlleFormula form "?" Expr then ":" Expr else
	| comprehension: "{" {VarDeclaration ","}+ decls "|" AlleFormula form "}"
	;

syntax VarDeclaration = varDecl: Variable var ":" Expr expr;

keyword Keywords = "no" | "lone" | "one" | "some" | "not" | "forall" | "exists";