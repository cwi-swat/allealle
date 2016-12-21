module relational::Imploder

import relational::Parser;
import relational::AST;
import relational::Syntax;

import ParseTree;

relational::AST::Problem implodeProblem(loc file) 			  = implode(#relational::AST::Problem, parseFile(file).top);
relational::AST::Problem implodeProblem(loc file, str x)  = implode(#relational::AST::Problem, parseFile(x, file).top);
relational::AST::Problem implodeProblem(str x)				    = implode(#relational::AST::Problem, parseString(x).top);

relational::AST::Problem implodeProblem(relational::Syntax::Problem p) = implode(#relational::AST::Problem, p);
