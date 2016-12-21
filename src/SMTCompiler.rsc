module SMTCompiler

import logic::Propositional;

import List; 

str compileDeclaredVariables(set[str] vars) = intercalate("\n", ["(declare-const <v> Bool)" | v <- vars]);

str compileAssertedFormula(Formula formula) = "(assert <compile(formula)>)";

str compile(\and(set[Formula] forms)) = "(and <("" | "<it> <compile(f)>" | f <- forms)>)";
str compile(\or(set[Formula] forms)) = "(or <("" | "<it> <compile(f)>" | f <- forms)>)";
str compile(\not(formula)) = "(not <compile(formula)>)";

str compile(\var(name)) = "<name>";
str compile(\false()) = "false";
str compile(\true()) = "true";

default str compile(Formula f) { throw "Compilation of <f> not supported"; }
