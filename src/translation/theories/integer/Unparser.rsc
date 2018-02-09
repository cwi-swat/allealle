module translation::theories::integer::Unparser

extend translation::Unparser;

import translation::theories::integer::AST; 

import List;

str unparse(intDom()) = "int";

str unparse(count())                                                = "count()";
str unparse(sum(str att))                                           = "sum(<att>)";
str unparse(max(str att))                                           = "max(<att>)";
str unparse(min(str att))                                           = "min(<att>)";
str unparse(avg(str att))                                           = "avg(<att>)";

str unparse(lt(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr))         = "(<unparse(lhsExpr)> \< <unparse(rhsExpr)>)";
str unparse(lte(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr))        = "(<unparse(lhsExpr)> \<= <unparse(rhsExpr)>)";
str unparse(gt(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr))         = "(<unparse(lhsExpr)> \> <unparse(rhsExpr)>)";
str unparse(gte(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr))        = "(<unparse(lhsExpr)> \>= <unparse(rhsExpr)>)";
  
str unparse(intLit(int i))                                          = "<i>";

str unparse(neg(CriteriaExpr e))                                    = "(-<unparse(e)>)";
str unparse(abs(CriteriaExpr e))                                    = "(|<unparse(e)>|)";
str unparse(multiplication(list[CriteriaExpr] terms))               = "(<intercalate(" * ", [unparse(t) | CriteriaExpr t <- terms])>)";
str unparse(division(CriteriaExpr lhs, CriteriaExpr rhs))           = "(<unparse(lhs)> / <unparse(rhs)>)";
str unparse(modulo(CriteriaExpr lhs, CriteriaExpr rhs))             = "(<unparse(lhs)> % <unparse(rhs)>)";
str unparse(addition(list[CriteriaExpr] terms))                     = "(<intercalate(" + ", [unparse(t) | CriteriaExpr t <- terms])>)";
str unparse(subtraction(CriteriaExpr lhs, CriteriaExpr rhs))        = "(<unparse(lhs)> - <unparse(rhs)>)";
