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
	;	
	
data Expr
	= intLit(int i)
	| neg(Expr expr)
	| multiplication(Expr lhs, Expr rhs)
	| division(Expr lhs, Expr rhs)
	| modulo(Expr lhs, Expr rhs)
	| addition(Expr lhs, Expr rhs)
  //| addition(list[Expr] terms)
	| subtraction(Expr lhs, Expr rhs)
  | sum(Expr expr)
  | car(Expr expr)
	;
	
//Expr addition(addition(list[Expr] terms), Expr rhs) = addition([*terms, rhs]) when bprintln("1");
//Expr addition(Expr lhs, addition(list[Expr] terms)) = addition([lhs, *terms]) when bprintln("2");
//Expr addition(Expr lhs, Expr rhs) = addition([lhs,rhs]) when bprintln("4");
