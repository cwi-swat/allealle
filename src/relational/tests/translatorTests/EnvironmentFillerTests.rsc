module relational::tests::translatorTests::EnvironmentFillerTests

import relational::Imploder;
import relational::AST;
import relational::Translator;

import Binder;

import logic::Propositional;

import IO;

test bool testUnaryRelations_noLowerBounds() {
	str problemStr = 
		"{a,b,c}
		'Rel:1 [{},{\<a\>,\<b\>,\<c\>}]
		";
		
	env = createInitialEnvironment(implodeProblem(problemStr));
	
	return env["Rel"][<relational(),["a"]>] == var("Rel_a") &&
			   env["Rel"][<relational(),["b"]>] == var("Rel_b") &&
			   env["Rel"][<relational(),["c"]>] == var("Rel_c");
}

test bool testUnaryRelations_withLowerBounds() {
	str problemStr = 
		"{a,b,c}
		'Rel:1 [{\<a\>},{\<a\>,\<b\>,\<c\>}]
		";
		
  env = createInitialEnvironment(implodeProblem(problemStr));
	
  return env["Rel"][<relational(),["a"]>] == \true() &&
         env["Rel"][<relational(),["b"]>] == var("Rel_b") &&
         env["Rel"][<relational(),["c"]>] == var("Rel_c");
}

test bool testUnaryRelations_notAllAtomsMapped() {
	str problemStr = 
		"{a,b,c}
		'Rel:1 [{},{\<a\>,\<b\>}]
		";
		
  env = createInitialEnvironment(implodeProblem(problemStr));
  
  return env["Rel"][<relational(),["a"]>] == var("Rel_a") &&
         env["Rel"][<relational(),["b"]>] == var("Rel_b") &&
         <relational(),["c"]> notin env["Rel"];
}

test bool testBinaryRelations_noLowerBounds() {
	str problemStr = 
		"{a,b,c}
		'Rel:2 [{},{\<a,b\>,\<a,c\>,\<b,c\>}]
		";
		
  env = createInitialEnvironment(implodeProblem(problemStr));
	
	return env["Rel"][<relational(),["a","b"]>] == var("Rel_a_b") &&
         env["Rel"][<relational(),["a","c"]>] == var("Rel_a_c") &&
         env["Rel"][<relational(),["b","c"]>] == var("Rel_b_c");
 }
 