module orig::Parser

import orig::Syntax;

import ParseTree;

start[Problem] parseFile(loc file) 			= parse(#start[Problem], file);
start[Problem] parseFile(str x, loc file) 	= parse(#start[Problem], x, file);
start[Problem] parseString(str x)			= parse(#start[Problem], x);
