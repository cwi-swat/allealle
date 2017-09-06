module translation::theories::integer::AST

extend translation::AST;
import IO;

// Integer theory extensions
data Domain = \int();

data Literal 
  = posInt(int i)
  | negInt(int i)
  ;
	
data AlleFormula
	= lt(AlleExpr lhsExpr, AlleExpr rhsExpr)
	| lte(AlleExpr lhExprs, AlleExpr rhsExpr)
	| gt(AlleExpr lhsExpr, AlleExpr rhsExpr)
	| gte(AlleExpr lhsExpr, AlleExpr rhsExpr)
	| intEqual(AlleExpr lhsExpr, AlleExpr rhsExpr)
	| intInequal(AlleExpr lhsExpr, AlleExpr rhsExpr)
	;	
	
data AlleExpr
	= intLit(int i)
	| neg(AlleExpr expr)
	| abs(AlleExpr expr)
	| multiplication(AlleExpr lhs, AlleExpr rhs)
  | multiplication(list[AlleExpr] terms)
	| division(AlleExpr lhs, AlleExpr rhs)
	| modulo(AlleExpr lhs, AlleExpr rhs)
	| addition(AlleExpr lhs, AlleExpr rhs)
  | addition(list[AlleExpr] terms)
	| subtraction(AlleExpr lhs, AlleExpr rhs)
  | sum(AlleExpr expr)
  | sumBind(AlleExpr bind, AlleExpr expr)
  | car(AlleExpr expr)
  | carBind(AlleExpr bind, AlleExpr expr)
	;
	
	
AlleExpr addition(addition(list[AlleExpr] terms), AlleExpr rhs) = addition([*terms, rhs]);
AlleExpr addition(AlleExpr lhs, addition(list[AlleExpr] terms)) = addition([lhs, *terms]);
AlleExpr addition(AlleExpr lhs, AlleExpr rhs) = addition([lhs,rhs]) when addition(_) !:= lhs && addition(_) !:= rhs;

AlleExpr multiplication(list[AlleExpr] terms, AlleExpr rhs) = multiplication([*terms, rhs]);
AlleExpr multiplication(AlleExpr lhs, multiplication(list[AlleExpr] terms)) = multiplication([lhs, *terms]);
AlleExpr multiplication(AlleExpr lhs, AlleExpr rhs) = multiplication([lhs,rhs]) when multiplication(_) !:= lhs && multiplication(_) !:= rhs;

//Expr rewrite(addition(addition(list[Expr] terms), Expr rhs)) = addition([*terms, rhs]);
//Expr rewrite(addition(Expr lhs, addition(list[Expr] terms))) = addition([lhs, *terms]);
//Expr rewrite(addition(Expr lhs, Expr rhs)) = addition([lhs,rhs]);
