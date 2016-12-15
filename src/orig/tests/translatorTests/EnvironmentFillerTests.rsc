module orig::tests::translatorTests::EnvironmentFillerTests

import orig::Imploder;
import orig::AST;
import orig::FormulaTranslator;

import IO;

private map[str, Binding] harnas(Problem p) {
 	map[str, Binding] envInternal = ();

	Binding lookupFromInternal(str name) = envInternal[name];
	bool addToInternal(str name, Binding vb) { envInternal[name] = vb; return true; }

	Environment env = <lookupFromInternal, addToInternal>;
	
	fillInitialEnvironment(p.uni, p.bounds, env);
	
	return envInternal;
}

test bool testUnaryRelations_noLowerBounds() {
	str problemStr = 
		"{a,b,c}
		'Rel:1 [{},{\<a\>,\<b\>,\<c\>}]
		";
		
	env = harnas(implodeProblem(problemStr));
	
	return 	env["Rel"][atom("a")] == {formula(var("Rel_a"))} &&
			env["Rel"][atom("b")] == {formula(var("Rel_b"))} &&
			env["Rel"][atom("c")] == {formula(var("Rel_c"))};
}

test bool testUnaryRelations_withLowerBounds() {
	str problemStr = 
		"{a,b,c}
		'Rel:1 [{\<a\>},{\<a\>,\<b\>,\<c\>}]
		";
		
	env = harnas(implodeProblem(problemStr));
	
	return 	env["Rel"][atom("a")] == {formula(\true())} &&
			env["Rel"][atom("b")] == {formula(var("Rel_b"))} &&
			env["Rel"][atom("c")] == {formula(var("Rel_c"))};
}

test bool testUnaryRelations_notAllAtomsMapped() {
	str problemStr = 
		"{a,b,c}
		'Rel:1 [{},{\<a\>,\<b\>}]
		";
		
	env = harnas(implodeProblem(problemStr));
	
	return 	env["Rel"][atom("a")] == {formula(var("Rel_a"))} &&
			env["Rel"][atom("b")] == {formula(var("Rel_b"))} &&
			env["Rel"][atom("c")] == {formula(\false())};
}

test bool testBinaryRelations_noLowerBounds() {
	str problemStr = 
		"{a,b,c}
		'Rel:2 [{},{\<a,b\>,\<a,c\>,\<b,c\>}]
		";
		
	env = harnas(implodeProblem(problemStr));
	
	bprintln(env["Rel"][atom("b")]);
	
	return 	env["Rel"][atom("a")] == {atom("b"),atom("c")};// &&
			//env["Rel"][atom("b")] == {formula(var("Rel_b"))} &&
			//env["Rel"][atom("c")] == {formula(var("Rel_c"))};
}