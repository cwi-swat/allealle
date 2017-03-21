module theories::relational::tests::translatorTests::BaseTester

import ide::Imploder;
extend theories::relational::Translator;

import theories::AST;
import theories::Binder;
import theories::Translator; 

import logic::Propositional;

import IO;

Formula translate(str problem) { 
	Problem p = implodeProblem(problem);

  Environment env = createInitialEnvironment(p);
  Formula result = translate(p, env);  

	return result;
}