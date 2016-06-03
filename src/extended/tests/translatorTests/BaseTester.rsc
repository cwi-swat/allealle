module extended::tests::translatorTests::BaseTester

import extended::Imploder;
import extended::AST;
import extended::Translator;

import logic::Integer;

import IO;

void testTranslation(loc file) {
	Problem p = implodeProblem(file);
	Formula result = translateExtended(p, createInitialEnvironment(p));  
	
	iprintln(result);
}

Formula translate(str problem) { 
	Problem p = implodeProblem(problem);
	return translateExtended(p, createInitialEnvironment(p));
}