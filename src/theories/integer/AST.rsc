module theories::integer::AST

extend theories::AST;

// Integer theory extensions
data Theory = intTheory();

data AtomValue = intVal(int val);

data Sort
	= intSort()
	;
	
data AlleFormula
	= lt(Expr lhsExpr, Expr rhsExpr)
	| lte(Expr lhExprs, Expr rhsExpr)
	| gt(Expr lhsExpr, Expr rhsExpr)
	| gte(Expr lhsExpr, Expr rhsExpr)
	| intEqual(Expr lhsExpr, Expr rhsExpr)
	| intInequal(Expr lhsExpr, Expr rhsExpr)
	;	
	
data Expr
	= intLit(int i)
	| multiplication(Expr lhs, Expr rhs)
	| division(Expr lhs, Expr rhs)
	| addition(Expr lhs, Expr rhs)
	| subtraction(Expr lhs, Expr rhs)
	;
