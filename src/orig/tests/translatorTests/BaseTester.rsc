module orig::tests::translatorTests::BaseTester

import orig::Imploder;
import orig::AST;
import orig::Translator;

import logic::Propositional;

import IO;

void testTranslation(loc file) {
	Problem p = implodeProblem(file);
	Formula result = translate(p, createInitialEnvironment(p));  
	
	iprintln(result);
}

Formula translate(str problem) { 
	Problem p = implodeProblem(problem);
	return translate(p, createInitialEnvironment(p));
}