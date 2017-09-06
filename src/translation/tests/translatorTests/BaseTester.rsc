module theories::tests::translatorTests::BaseTester

extend theories::Translator;

import ide::Imploder;

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