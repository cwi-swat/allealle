module extended::AST

extend orig::AST;

data RelationalBound = relationalBound(str relName, Sort sort, int arity, list[Tuple] lowerBounds, list[Tuple] upperBounds);

// Integer theory extensions
data Sort
	= intSort()
	;
	
data Formula
	= lt(Expr lhsExpr, Expr rhsExpr)
	| lte(Expr lhExprs, Expr rhsExpr)
	| gt(Expr lhsExpr, Expr rhsExpr)
	| gte(Expr lhsExpr, Expr rhsExpr)
	| intEqual(Expr lhsExpr, Expr rhsExpr)
	;	
	
data Expr
	= intLit(int i)
	//| intProjection(Expr expr)
	| multiplication(Expr lhs, Expr rhs)
	| division(Expr lhs, Expr rhs)
	| addition(Expr lhs, Expr rhs)
	| subtraction(Expr lhs, Expr rhs)
	;
