module translation::theories::string::Imploder

import translation::Syntax;
import translation::theories::string::AST; 

import ParseTree;
import String;

translation::AST::Domain implode((Domain)`str`) = strDom();  

translation::AST::AlleLiteral implode((Literal)`<StrLit s>`) = strLit("<s>");  