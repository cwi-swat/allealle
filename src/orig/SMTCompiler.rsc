module orig::SMTCompiler

import logic::Propositional;

import List;

str compileToSMT(Formula formula) {
	// gather all used variables
	set[str] varNames = {name | /var(str name) := formula};
	
	// declare all variables
	str smt = intercalate("\n", ["(declare-const <name> Bool)" | name <- varNames]);

	smt += 	"(assert <compile(formula)>)";
	
	return smt;
}

str compile(\and(set[Formula] forms)) = "(and <intercalate(" ", [compile(f) | f <- forms])>)";
str compile(\or(set[Formula] forms)) = "(or <intercalate(" ", [compile(f) | f <- forms])>)";
str compile(\not(formula)) = "(not <compile(formula)>)";
str compile(\var(name)) = name;
str compile(\true()) = "true";
str compile(\false()) = "false";

default str compile(Formula f) { throw "Compilation of <f> not supported"; }