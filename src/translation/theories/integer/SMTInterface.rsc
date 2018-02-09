module translation::theories::integer::SMTInterface

extend translation::SMTInterface;

import smtlogic::Ints;

import List;
import String; 

str preamble(\int()) = aggregateIntFunctions();  

str compileVariableDeclaration(<str name, \int()>) = "(declare-const <name> Int)";

str compile(\int(int i))                          = "<i>"; 

str compile(neg(Term e))                          = "(- <compile(e)>)"; 
str compile(abs(Term e))                          = "(abs <compile(e)>)"; 

str compile(addition(list[Term] terms))           = "(+ <for (t <- terms) {><compile(t)> <}>)";
str compile(multiplication(list[Term] terms))     = "(* <for (t <- terms) {><compile(t)> <}>)";
str compile(division(Term lhs, Term rhs))         = "(div <compile(lhs)> <compile(rhs)>)"; 
str compile(modulo(Term lhs, Term rhs))           = "(mod <compile(lhs)> <compile(rhs)>)";

str compile(lt(Term lhs, Term rhs))               = "(\< <compile(lhs)> <compile(rhs)>)";
str compile(lte(Term lhs, Term rhs))              = "(\<= <compile(lhs)> <compile(rhs)>)";
str compile(gt(Term lhs, Term rhs))               = "(\> <compile(lhs)> <compile(rhs)>)";
str compile(gte(Term lhs, Term rhs))              = "(\>= <compile(lhs)> <compile(rhs)>)";


Term getValue((SmtValue)`<Val v>`, <str _, \int()>) = lit(\int(toInt("<v>")));
Term getValue((SmtValue)`(- <Val v>)`, <str _, \int()>) = neg(lit(\int(toInt("<v>"))));
 
str negateAttribute(str varName, lit(\int(int i))) = "(not (= <varName> <i>))";
str negateAttribute(str varName, neg(lit(\int(int i)))) = "(not (= <varName> (- <i>)))";

str aggregateIntFunctions() =
  "(define-fun _iSum ((exsts Bool) (val Int) (accum Int)) Int
  '  (ite exsts (+ val accum) accum)
  ')
  '
  '(define-fun _startVal ((exsts Bool) (val Int) (accum Int)) Int
  ' (ite exsts val accum)
  ')
  '
  '(define-fun _iMax ((exsts Bool) (val Int) (accum Int)) Int
  ' (ite (\> accum val) accum (ite exsts val accum))
  ')
  '
  '(define-fun _iMin ((exsts Bool) (val Int) (accum Int)) Int
  ' (ite (\< accum val) accum (ite exsts val accum))
  ')
  '
  '(define-fun _count ((exsts Bool) (accum Int)) Int
  ' (ite exsts (+ accum 1) accum)
  ')";