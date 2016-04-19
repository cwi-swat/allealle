module orig::Imploder

import orig::Parser;
import orig::AST;

import ParseTree;

Problem implodeProblem(loc file) 			= implode(#Problem, parseFile(file).top);
Problem implodeProblem(loc file, str x) 	= implode(#Problem, parseFile(x, file).top);
Problem implodeProblem(str x)				= implode(#Problem, parseString(x).top);