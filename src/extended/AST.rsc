module extended::AST

extend orig::AST;

data RelationalBound = relationalBound(str relName, Sort sort, int arity, list[Tuple] lowerBounds, list[Tuple] upperBounds);

// Integer theory extensions
data Sort
	= intSort()
	;
	
data Formula
	= lt(Expr lhs, Expr rhs)
	| lte(Expr lhs, Expr rhs)
	| gt(Expr lhs, Expr rhs)
	| gte(Expr lhs, Expr rhs)
	| intEqual(Expr lhs, Expr rhs)
	;	
	
data Expr
	= intLit(int i)
	| intVar(str name)
	| multiplication(Expr lhs, Expr rhs)
	| division(Expr lhs, Expr rhs)
	| addition(Expr lhs, Expr rhs)
	| subtraction(Expr lhs, Expr rhs)
	;
