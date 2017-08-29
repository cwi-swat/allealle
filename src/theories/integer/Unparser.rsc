module theories::integer::Unparser

extend theories::Unparser;

import theories::integer::AST; 
import List;

str unparse(intTheory()) = "int";

str unparse(intExpr(Expr expr)) = "<unparse(expr)>";

str unparse(lt(Expr lhsExpr, Expr rhsExpr))         = "(<unparse(lhsExpr)> \< <unparse(rhsExpr)>)";
str unparse(lte(Expr lhsExpr, Expr rhsExpr))        = "(<unparse(lhsExpr)> \<= <unparse(rhsExpr)>)";
str unparse(gt(Expr lhsExpr, Expr rhsExpr))         = "(<unparse(lhsExpr)> \> <unparse(rhsExpr)>)";
str unparse(gte(Expr lhsExpr, Expr rhsExpr))        = "(<unparse(lhsExpr)> \>= <unparse(rhsExpr)>)";
str unparse(intEqual(Expr lhsExpr, Expr rhsExpr))   = "(<unparse(lhsExpr)> = <unparse(rhsExpr)>)";
str unparse(intInequal(Expr lhsExpr, Expr rhsExpr)) = "(<unparse(lhsExpr)> != <unparse(rhsExpr)>)";
  
str unparse(intLit(int i))                               = "<i>";
str unparse(neg(Expr e))                                 = "(-<unparse(e)>)";
str unparse(abs(Expr e))                                 = "(|<unparse(e)>|)";
//str unparse(multiplication(Expr lhs, Expr rhs))          = "(<unparse(lhs)> * <unparse(rhs)>)";
str unparse(multiplication(list[Expr] terms))            = "(<intercalate(" * ", [unparse(t) | Expr t <- terms])>)";
str unparse(division(Expr lhs, Expr rhs))                = "(<unparse(lhs)> / <unparse(rhs)>)";
str unparse(modulo(Expr lhs, Expr rhs))                  = "(<unparse(lhs)> % <unparse(rhs)>)";
str unparse(addition(list[Expr] terms))                  = "(<intercalate(" + ", [unparse(t) | Expr t <- terms])>)";
//str unparse(addition(Expr lhs, Expr rhs))                = "(<unparse(lhs)> + <unparse(rhs)>)";
str unparse(subtraction(Expr lhs, Expr rhs))             = "(<unparse(lhs)> - <unparse(rhs)>)";
str unparse(sum(Expr expr))                              = "(sum(<unparse(expr)>))";
str unparse(sumBind(Expr bind, Expr e))                  = "(sumBind(<unparse(bind)>,<unparse(e)>))";
str unparse(car(Expr expr))                              = "(#<unparse(expr)>)";
str unparse(carBind(Expr bind, Expr e))                  = "(#(<unparse(bind)>,<unparse(e)>))";
