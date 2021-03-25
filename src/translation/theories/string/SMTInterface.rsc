module translation::theories::string::SMTInterface

import translation::SMTValueSyntax;

import smtlogic::Core;
import smtlogic::Strings;

import List;
import String; 

str preamble(Sort::\str()) 
  = "; STRING PREAMBLE
    '(define-fun cus.int.to.str ((i Int)) String
    '  (ite (\< i 0) (str.++ \"-\" (int.to.str (* (- 1) i) )) (int.to.str i))
    ')
    '
    '(define-fun cus.str.to.int ((s String)) Int
    '  (ite (str.prefixof \"-\" s) (- (str.to.int (str.substr s (- (str.len s) 1) 1) )) (str.to.int s))
    ')";  

str compileVariableDeclaration(<str name, Sort::\str()>) = "(declare-const <name> String)";

@memo str compile(\str(str s))                          = "<s>"; 
@memo str compile(strLength(Term t))                    = "(str.len <compile(t)>)"; 
@memo str compile(strToInt(Term t))                     = "(str.to.int <compile(t)>)"; 
@memo str compile(intToStr(Term t))                     = "(int.to.str <compile(t)>)"; 
@memo str compile(strConcat(list[Term] terms))          = "(str.++ <intercalate(" ", [compile(t) | t <- terms])>)"; 
@memo str compile(substr(Term e, Term offset, Term length)) = "(str.substr <compile(e)> <compile(offset)> <compile(length)>)"; 

@memo str compileWithoutIden(\str(str s))                   = "<s>"; 
@memo str compileWithoutIden(strLength(Term t))             = "(str.len <compileWithoutIden(t)>)"; 
@memo str compileWithoutIden(strToInt(Term t))              = "(str.to.int <compileWithoutIden(t)>)"; 
@memo str compileWithoutIden(intToStr(Term t))              = "(int.to.str <compileWithoutIden(t)>)"; 
@memo str compileWithoutIden(strConcat(list[Term] terms))   = "(str.++ <intercalate(" ", [compileWithoutIden(t) | t <- terms])>)"; 
@memo str compileWithoutIden(substr(Term e, Term offset, Term length)) = "(str.substr <compileWithoutIden(e)> <compileWithoutIden(offset)> <compileWithoutIden(length)>)"; 

Term getValue((SmtValue)`"<StringCharacter* chars>"`, <str _, Sort::\str()>) = lit(\str("<chars>"));

str negateVariable(str varName, lit(\str(str s))) = "(not (= <varName> \"<s>\"))";
