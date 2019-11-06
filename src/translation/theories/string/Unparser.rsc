module translation::theories::string::Unparser

import translation::theories::string::AST; 

str unparse(strDom())       = "str";
str unparse(strLit(str s))  = "<s>";