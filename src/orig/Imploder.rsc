module orig::Imploder

import orig::Parser;
import orig::AST;
import orig::Syntax;

import ParseTree;

orig::AST::Problem implodeProblem(loc file) 			= implode(#Problem, parseFile(file).top);
orig::AST::Problem implodeProblem(loc file, str x) 		= implode(#Problem, parseFile(x, file).top);
orig::AST::Problem implodeProblem(str x)				= implode(#Problem, parseString(x).top);

orig::AST::Problem implodeProblem(orig::Syntax::Problem p) = implode(#Problem, p);