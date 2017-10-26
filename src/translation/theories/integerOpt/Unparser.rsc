module translation::theories::integerOpt::Unparser

extend translation::theories::integer::Unparser;
import translation::theories::integerOpt::AST; 

str unparse(minimize(AlleExpr expr)) = "(minimize <unparse(expr)>)";
str unparse(maximize(AlleExpr expr)) = "(maximize <unparse(expr)>)";


