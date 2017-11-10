module translation::theories::integer::Unparser

extend translation::Unparser;

import translation::theories::integer::AST; 

import List;

str unparse(\int()) = "int";

str unparse(lt(AlleExpr lhsExpr, AlleExpr rhsExpr))         = "(<unparse(lhsExpr)> \< <unparse(rhsExpr)>)";
str unparse(lte(AlleExpr lhsExpr, AlleExpr rhsExpr))        = "(<unparse(lhsExpr)> \<= <unparse(rhsExpr)>)";
str unparse(gt(AlleExpr lhsExpr, AlleExpr rhsExpr))         = "(<unparse(lhsExpr)> \> <unparse(rhsExpr)>)";
str unparse(gte(AlleExpr lhsExpr, AlleExpr rhsExpr))        = "(<unparse(lhsExpr)> \>= <unparse(rhsExpr)>)";
str unparse(intEqual(AlleExpr lhsExpr, AlleExpr rhsExpr))   = "(<unparse(lhsExpr)> = <unparse(rhsExpr)>)";
str unparse(intInequal(AlleExpr lhsExpr, AlleExpr rhsExpr)) = "(<unparse(lhsExpr)> != <unparse(rhsExpr)>)";
str unparse(distinct(AlleExpr e))                           = "(distinct(<unparse(e)>)";
  
str unparse(intLit(int i))                                  = "<i>";
str unparse(neg(AlleExpr e))                                = "(-<unparse(e)>)";
str unparse(abs(AlleExpr e))                                = "(|<unparse(e)>|)";
str unparse(multiplication(list[AlleExpr] terms))           = "(<intercalate(" * ", [unparse(t) | AlleExpr t <- terms])>)";
str unparse(division(AlleExpr lhs, AlleExpr rhs))           = "(<unparse(lhs)> / <unparse(rhs)>)";
str unparse(modulo(AlleExpr lhs, AlleExpr rhs))             = "(<unparse(lhs)> % <unparse(rhs)>)";
str unparse(addition(list[AlleExpr] terms))                 = "(<intercalate(" + ", [unparse(t) | AlleExpr t <- terms])>)";
str unparse(subtraction(AlleExpr lhs, AlleExpr rhs))        = "(<unparse(lhs)> - <unparse(rhs)>)";
str unparse(sum(AlleExpr expr))                             = "(sum(<unparse(expr)>))";
str unparse(car(AlleExpr expr))                             = "(#<unparse(expr)>)";
