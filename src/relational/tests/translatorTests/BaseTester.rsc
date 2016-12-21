module relational::tests::translatorTests::BaseTester

import relational::Imploder;
import relational::Translator;

import AST;
import Binder;
import Translator;

import logic::Propositional;

import IO;

void testTranslation(loc file) {
	Problem p = implodeProblem(file);
  
  Translator relationalTranslator = getRelationalTranslator();
  
  Environment	env = createInitialEnvironment(p, [relationalTranslator]);
	Formula result = translate(p, env, [relationalTranslator]);  
	
	iprintln(result);
}

Formula translate(str problem) { 
	Problem p = implodeProblem(problem);

  Translator relationalTranslator = getRelationalTranslator();

  Environment env = createInitialEnvironment(p, [relationalTranslator]);
  Formula result = translate(p, env, [relationalTranslator]);  

	return result;
}