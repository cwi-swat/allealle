module smtlogic::Strings

import smtlogic::Core;

data Sort
  = \str()
  ;

data Term
  = strLength(Term e)
  | strToInt(Term e)
  | intToStr(Term e)
  | strConcat(list[Term] terms)
  | substr(Term e, Term offset, Term length)
  ;

data Literal
  = \str(str s)
  ;

  