module smtlogic::Strings

import smtlogic::Core;

import IO;

data Sort
  = \str()
  ;

data Term
  = strLength(Term e)
  | strToInt(Term e)
  | intToStr(Term e)
  | strConcat(list[Term] terms)
  ;

data Literal
  = \str(str s)
  ;

  