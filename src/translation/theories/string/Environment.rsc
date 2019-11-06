module translation::theories::string::Environment

import translation::theories::string::AST;

import smtlogic::Core;
import smtlogic::Strings; 
 
Literal convertToLit(strLit(str s)) = \str(s);
Term convertToVar(str varName, strDom()) = var(varName, Sort::\str());

Sort domain2Sort(strDom()) = Sort::\str();

