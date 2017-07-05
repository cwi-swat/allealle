module theories::integer::AST

extend theories::AST;
import IO;

// Integer theory extensions
data Theory = intTheory();

data AtomValue 
  = intExpr(Expr expr)
  ;
	
data AlleFormula
	= lt(Expr lhsExpr, Expr rhsExpr)
	| lte(Expr lhExprs, Expr rhsExpr)
	| gt(Expr lhsExpr, Expr rhsExpr)
	| gte(Expr lhsExpr, Expr rhsExpr)
	| intEqual(Expr lhsExpr, Expr rhsExpr)
	| intInequal(Expr lhsExpr, Expr rhsExpr)
	| minimize(Expr expr)
	;	
	
data Expr
	= intLit(int i)
	| neg(Expr expr)
	| multiplication(Expr lhs, Expr rhs)
  | multiplication(list[Expr] terms)
	| division(Expr lhs, Expr rhs)
	| modulo(Expr lhs, Expr rhs)
	| addition(Expr lhs, Expr rhs)
  | addition(list[Expr] terms)
	| subtraction(Expr lhs, Expr rhs)
  | sum(Expr expr)
  | car(Expr expr)
	;
	
	
Expr addition(list[Expr] terms, Expr rhs) = addition([*terms, rhs]);
Expr addition(Expr lhs, addition(list[Expr] terms)) = addition([lhs, *terms]);
Expr addition(Expr lhs, Expr rhs) = addition([lhs,rhs]) when addition(_) !:= lhs && addition(_) !:= rhs;

Expr multiplication(list[Expr] terms, Expr rhs) = multiplication([*terms, rhs]);
Expr multiplication(Expr lhs, multiplication(list[Expr] terms)) = multiplication([lhs, *terms]);
Expr multiplication(Expr lhs, Expr rhs) = multiplication([lhs,rhs]) when multiplication(_) !:= lhs && multiplication(_) !:= rhs;

//Expr rewrite(addition(addition(list[Expr] terms), Expr rhs)) = addition([*terms, rhs]);
//Expr rewrite(addition(Expr lhs, addition(list[Expr] terms))) = addition([lhs, *terms]);
//Expr rewrite(addition(Expr lhs, Expr rhs)) = addition([lhs,rhs]);
