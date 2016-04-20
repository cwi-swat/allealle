module orig::smt::Translator

import orig::Translator;

import List;
import IO;

//data SATFormula
//	= \constant(Atom a)
//	| \true()
//	| \false()
//	| var(str id)
//	| not(SATFormula formula)
//	| and(SATFormula lhs, SATFormula rhs)
//	| or(SATFormula lhs, SATFormula rhs)
//	| ite(SATFormula caseCond, SATFormula thenCond, SATFormula elseCond)
//	| empty()
//	;

void compileAndSave(SATFormula formula, map[str, Binding] environment, loc output) =
	writeFile(|project://allealle/output/out.smt2|, compile(formula, environment));

str compile(SATFormula formula, map[str, Binding] environment) {
	// gather all variables
	set[str] varNames = {name | /var(str name) := formula};
	
	// declare all variables
	str smt = intercalate("\n", ["(declare-const <name> Bool)" | name <- varNames]);

	smt += 	"
			'(assert <compile(formula)>)
			'(check-sat)\n";	
	
	smt += "(get-value (<intercalate(" ", [name | name <- varNames])>))";
	
	return smt;
}

str compile(and(lhs, rhs)) = 	"(and 
								'  <compile(lhs)> 
								'  <compile(rhs)>
								')";
str compile(or(lhs, rhs)) = 	"(or 
								'  <compile(lhs)> 
								'  <compile(rhs)>
								')";
str compile(not(formula)) = "(not <compile(formula)>)";
str compile(var(name)) = name;
str compile(\true()) = "true";
str compile(\false()) = "false";
str compile(ite(caseCond, thenCond, elseCond)) = "(ite <compile(caseCond)>
												 '	<compile(thenCond)>
												 '	<compile(elseCond)>)\n";