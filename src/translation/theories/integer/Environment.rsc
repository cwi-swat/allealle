module translation::theories::integer::Environment

extend translation::Environment;

import translation::theories::integer::AST;
import smtlogic::Ints; 
 
Literal convertToLit(intLit(int i)) = \int(i);
Term convertToVar(str varName, intDom()) = var(varName, \int());

Sort domain2Sort(intDom()) = \int();

