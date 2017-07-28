module theories::integerOpt::Unparser

extend theories::integer::Unparser;
import theories::integerOpt::AST; 

str unparse(minimize(Expr expr)) = "(minimize <unparse(expr)>)";
str unparse(maximize(Expr expr)) = "(maximize <unparse(expr)>)";


