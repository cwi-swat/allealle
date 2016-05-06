module orig::SMTCompiler

import logic::Propositional;

import List;

alias SMTCompilerResult = tuple[str smtFormula, map[str label, Formula f] labels];

SMTCompilerResult compileToSMT(Formula formula) {
	int label = 0;
	
	map[str, Formula] labeledFormulas = ();
	str addLabeledFormula(Formula orig) {
		label += 1; 
		labeledFormulas += ("l<label>":orig);
		
		return "l<label>";
	} 
	
	// declare all variables
	//str smt = ("" | "<it>\n(assert <compile(c, addLabeledFormula)>)" | Formula c <- clauses);
	str smt = "(assert <compile(formula, addLabeledFormula)>)";
	return <smt, labeledFormulas>;
}

str compile(a:\and(set[Formula] forms), str (Formula) labeler) = "(! (and <intercalate(" ", [compile(f, labeler) | f <- forms])>) :named <labeler(a)>)";
str compile(a:\or(set[Formula] forms), str (Formula) labeler) = "(! (or <intercalate(" ", [compile(f, labeler) | f <- forms])>) :named <labeler(a)>)";
str compile(a:\not(formula), str (Formula) labeler) = "(! (not <compile(formula, labeler)>) :named <labeler(a)>)";
str compile(a:\var(name), str (Formula) labeler) = "(! <name> :named <labeler(a)>)";
str compile(\false(), str (Formula) labeler) = "false";
str compile(\true(), str (Formula) labeler) = "true";
default str compile(Formula f, str (Formula) labeler) { throw "Compilation of <f> not supported"; }

