module translation::theories::string::SMTInterface

import translation::SMTValueSyntax;

import smtlogic::Core;
import smtlogic::Strings;

import List;
import String; 

str preamble(Sort::\str()) = "";  

str compileVariableDeclaration(<str name, Sort::\str()>) = "(declare-const <name> String)";

@memo str compile(\str(str s))                          = "<s>"; 

@memo
str compileWithoutIden(\str(str s))                      = "<s>"; 

Term getValue((SmtValue)`"<Val v>"`, <str _, Sort::\str()>) = lit(\str("<v>"));
Term getValue((SmtValue)`""`, <str _, Sort::\str()>) = lit(\str(""));
 
str negateVariable(str varName, lit(\str(str s))) = "(not (= <varName> \"<s>\"))";
