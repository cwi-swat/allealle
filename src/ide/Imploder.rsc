module ide::Imploder

import ide::CombinedSyntax;
import ide::CombinedAST;
import ide::Parser;

import ParseTree;

//ide::CombinedAST::Expr addition(list[ide::CombinedAST::Expr] terms, ide::CombinedAST::Expr rhs) = addition([*terms, rhs]);
//ide::CombinedAST::Expr addition(ide::CombinedAST::Expr lhs, addition(list[ide::CombinedAST::Expr] terms)) = addition([lhs, *terms]);
//ide::CombinedAST::Expr addition(ide::CombinedAST::Expr lhs, ide::CombinedAST::Expr rhs) = addition([lhs,rhs]) when addition(_) !:= lhs && addition(_) !:= rhs;
//
//ide::CombinedAST::Expr multiplication(list[ide::CombinedAST::Expr] terms, ide::CombinedAST::Expr rhs) = multiplication([*terms, rhs]);
//ide::CombinedAST::Expr multiplication(ide::CombinedAST::Expr lhs, multiplication(list[ide::CombinedAST::Expr] terms)) = multiplication([lhs, *terms]);
//ide::CombinedAST::Expr multiplication(ide::CombinedAST::Expr lhs, ide::CombinedAST::Expr rhs) = multiplication([lhs,rhs]) when multiplication(_) !:= lhs && multiplication(_) !:= rhs;

ide::CombinedAST::Problem implodeProblem(loc file)         = implode(#ide::CombinedAST::Problem, parseFile(file).top);
ide::CombinedAST::Problem implodeProblem(loc file, str x)  = implode(#ide::CombinedAST::Problem, parseFile(x, file).top);
ide::CombinedAST::Problem implodeProblem(str x)            = implode(#ide::CombinedAST::Problem, parseString(x).top);

ide::CombinedAST::Problem implodeProblem(ide::CombinedSyntax::Problem p) = implode(#ide::CombinedAST::Problem, p);
