module translation::theories::integer::AST

extend translation::AST;
import IO;

// Integer theory extensions
data Domain = intDom();

data AlleLiteral 
  = intLit(int i)
  ;
	
data AggregateFunction
  = count()
  | sum(str att)
  | max(str att)
  | min(str att)
  | avg(str att)
  ;	
	
data Criteria
  = lt(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)
  | lte(CriteriaExpr lhExprs, CriteriaExpr rhsExpr)
  | gt(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)
  | gte(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)
  ;

data CriteriaExpr
	= abs(CriteriaExpr expr)
	| neg(CriteriaExpr expr)
  | multiplication(list[CriteriaExpr] terms)
	| division(CriteriaExpr lhs, CriteriaExpr rhs)
	| modulo(CriteriaExpr lhs, CriteriaExpr rhs)
  | addition(list[CriteriaExpr] terms)
	| subtraction(CriteriaExpr lhs, CriteriaExpr rhs)
	;
	
CriteriaExpr addition(addition(list[CriteriaExpr] terms), CriteriaExpr rhs) = addition([*terms, rhs]);
CriteriaExpr addition(CriteriaExpr lhs, addition(list[CriteriaExpr] terms)) = addition([lhs, *terms]);
CriteriaExpr addition(CriteriaExpr lhs, CriteriaExpr rhs) = addition([lhs,rhs]) when addition(_) !:= lhs && addition(_) !:= rhs;

CriteriaExpr multiplication(multiplication(list[CriteriaExpr] terms), CriteriaExpr rhs) = multiplication([*terms, rhs]);
CriteriaExpr multiplication(CriteriaExpr lhs, multiplication(list[CriteriaExpr] terms)) = multiplication([lhs, *terms]);
CriteriaExpr multiplication(CriteriaExpr lhs, CriteriaExpr rhs) = multiplication([lhs,rhs]) when multiplication(_) !:= lhs && multiplication(_) !:= rhs;