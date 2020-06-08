module translation::theories::string::SMTInterface

import translation::SMTValueSyntax;

import smtlogic::Core;
import smtlogic::Strings;

import List;
import String; 

str preamble(Sort::\str()) = "";  

str compileVariableDeclaration(<str name, Sort::\str()>) = "(declare-const <name> String)";

@memo str compile(\str(str s))                          = "<s>"; 
@memo str compile(strLength(Term t))                    = "(str.len <compile(t)>)"; 
@memo str compile(strToInt(Term t))                     = "(str.to.int <compile(t)>)"; 
@memo str compile(intToStr(Term t))                     = "(int.to.str <compile(t)>)"; 
@memo str compile(strConcat(list[Term] terms))          = "(str.++ <intercalate(" ", [compile(t) | t <- terms])>)"; 
@memo str compile(substr(Term e, Term offset, Term length)) = "(str.substr <compile(e)> <compile(offset)> <compile(length)>)"; 

@memo str compileWithoutIden(\str(str s))                   = "<s>"; 
@memo str compileWithoutIden(strLength(Term t))             = "(str.len <compile(t)>)"; 
@memo str compileWithoutIden(strToInt(Term t))              = "(str.to.int <compile(t)>)"; 
@memo str compileWithoutIden(intToStr(Term t))              = "(int.to.str <compile(t)>)"; 
@memo str compileWithoutIden(strConcat(list[Term] terms))   = "(str.++ <intercalate(" ", [compile(t) | t <- terms])>)"; 
@memo str compileWithoutIden(substr(Term e, Term offset, Term length)) = "(str.substr <compile(e)> <compile(offset)> <compile(length)>)"; 

Term getValue((SmtValue)`"<Val v>"`, <str _, Sort::\str()>) = lit(\str("<v>"));
Term getValue((SmtValue)`""`, <str _, Sort::\str()>) = lit(\str(""));
 
str negateVariable(str varName, lit(\str(str s))) = "(not (= <varName> \"<s>\"))";
