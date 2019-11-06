module ide::Imploder

import ide::Parser;
import ide::UnicodeRewriter;

import translation::Syntax;
import translation::AST;

import translation::Imploder;

import ParseTree;
import IO;

translation::AST::Problem implodeProblem(loc file)         = implodeProblemm(parseFile(file).top);
translation::AST::Problem implodeProblem(loc file, str x)  = implodeProblemm(parseFile(x, file).top);
translation::AST::Problem implodeProblem(str x)            = implodeProblemm(parseString(x).top);

translation::AST::Problem implodeProblemm(translation::Syntax::Problem p) = implodeProblem(unicodeRewriteTree(p));