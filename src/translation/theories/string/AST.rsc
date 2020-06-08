module translation::theories::string::AST

// String theory extensions
data Domain = strDom();

data CriteriaExpr
  = strLength(CriteriaExpr expr)
  | strToInt(CriteriaExpr expr)
  | intToStr(CriteriaExpr expr)
  | substr(CriteriaExpr expr, CriteriaExpr offset, CriteriaExpr length)
  | strConcat(list[CriteriaExpr] exprs)
  ;

data AlleLiteral 
  = strLit(str s)
  ;
  
CriteriaExpr strConcat(list[CriteriaExpr] exprs, CriteriaExpr rhs) = strConcat([*exprs,rhs]);
CriteriaExpr strConcat(CriteriaExpr lhs, list[CriteriaExpr] exprs) = strConcat([lhs,*exprs]);
CriteriaExpr strConcat(CriteriaExpr lhs, CriteriaExpr rhs) = strConcat([lhs,rhs]);