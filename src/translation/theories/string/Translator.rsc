module translation::theories::string::Translator

import smtlogic::Strings;

import translation::Relation;
import translation::theories::string::AST;

import Map;
import Set;

Literal translateLiteral(strLit(str s)) = \str(s);
  
Relation emptyRel(Heading h) = <h, (), {}>;