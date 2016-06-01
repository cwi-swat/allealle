module extended::SMTCompiler

import logic::Propositional;

str compileDeclaredVariables(set[str] vars) = 	"(declare-sort Rel) 
										'<("" | "<it>\n(declare-const <v> Rel)" | v <- vars)>
										";

str compileAssertedFormula(Formula formula) =
	"(declare-fun boolVal (Rel) Bool)
	'(assert <compile(formula)>)";

@memo
str compile(\and(set[Formula] forms)) = "(and <("" | "<it> <compile(f)>" | f <- forms)>)";
@memo
str compile(\or(set[Formula] forms)) = "(or <("" | "<it> <compile(f)>" | f <- forms)>)";
@memo
str compile(\not(formula)) = "(not <compile(formula)>)";
@memo
str compile(\var(name)) = "(boolVal <name>)";
str compile(\false()) = "false";
str compile(\true()) = "true";
default str compile(Formula f) { throw "Compilation of <f> not supported"; }
