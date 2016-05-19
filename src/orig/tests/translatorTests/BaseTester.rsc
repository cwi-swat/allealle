module orig::tests::translatorTests::BaseTester

import orig::Imploder;
import orig::AST;
import orig::Translator;

import logic::Propositional;

import IO;

void testTranslation(loc file) {
	Problem p = implodeProblem(file);
	TranslationResult result = translate(p);  
	
	iprintln(result.formula);
	println(result.environment);
	
	compileAndSave(result.formula, result.environment, |project://allealle/output/out.smt2|);
}

TranslationResult translate(str problem) = translate(implodeProblem(problem));