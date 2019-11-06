module translation::theories::string::AST

// String theory extensions
data Domain = strDom();

data AlleLiteral 
  = strLit(str s)
  ;