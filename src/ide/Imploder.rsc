module ide::Imploder

import ide::CombinedSyntax;
import ide::CombinedAST;
import ide::Parser;

import ParseTree;

ide::CombinedAST::Problem implodeProblem(loc file)         = implode(#ide::CombinedAST::Problem, parseFile(file).top);
ide::CombinedAST::Problem implodeProblem(loc file, str x)  = implode(#ide::CombinedAST::Problem, parseFile(x, file).top);
ide::CombinedAST::Problem implodeProblem(str x)            = implode(#ide::CombinedAST::Problem, parseString(x).top);

ide::CombinedAST::Problem implodeProblem(ide::CombinedSyntax::Problem p) = implode(#ide::CombinedAST::Problem, p);
