module translation::theories::integer::SMTInterface

extend translation::SMTInterface;

import smtlogic::Ints;

import List;
import String; 

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
 
str negateAttribute(str varName, lit(\int(int i))) = "(not (= <varName> <i>))";
str negateAttribute(str varName, neg(lit(\int(int i)))) = "(not (= <varName> (- <i>)))";
