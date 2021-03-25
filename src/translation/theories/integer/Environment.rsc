module translation::theories::integer::Environment

import translation::theories::integer::AST;
import smtlogic::Ints; 
 
Literal convertToLit(intLit(int i)) = \int(i);
Literal convertToLit(negIntLit(int i)) = \int(-i);

Term convertToVar(str varName, intDom()) = var(varName, Sort::\int());

Sort domain2Sort(intDom()) = Sort::\int();

