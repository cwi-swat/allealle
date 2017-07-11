module theories::integerOpt::Unparser

extend theories::integer::Unparser;

str unparse(minimize(Expr expr)) = "(minimize <unparse(expr)>)";
str unparse(maximize(Expr expr)) = "(maximize <unparse(expr)>)";


