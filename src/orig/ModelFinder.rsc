module orig::ModelFinder

import logic::Propositional;

import orig::AST;
import orig::Imploder;
import orig::Translator;
import orig::SMTCompiler;
import logic::CNFConverter;
import orig::SolverRunner;

import util::Benchmark;
import IO;
import List;

alias PID = int;

data ModelFinderResult 
	= sat(Environment currentModel, Universe universe, Environment () nextModel, void () stop)
	| unsat(set[Formula] unsatCore)
	| trivial(bool sat)
	;

ModelFinderResult checkInitialSolution(Problem problem) {
	print("Translating problem to SAT formula...");
	tuple[TranslationResult result, int time] t = benchmark(translate, problem);
	print("done\n");
	println("Translation to SAT formula took: <(t.time/1000000)> ms");
	
	println("SAT Formula:");
	iprintln(t.result.formula); 
	 
	//print("Converting to CNF...");
	//tuple[Formula formula, int time] cnf = <t.result.formula, t.time>; //benchmark(convertToCNF, t.result.formula);

	if (t.result.formula == \false()) {
		return trivial(false);
	}

	return runInSolver(problem, t.result);
}

private ModelFinderResult runInSolver(Problem originalProblem, TranslationResult translation) {
	PID solverPid = startSolver();
	void stop() {
		stopSolver(solverPid);
	}
	
	set[str] vars = {name | /var(str name) := translation.formula};
	
	print("Solving by Z3...");
	tuple[CheckSatResult result, int time] solving = benchmark(isSatisfiable, solverPid, vars, translation.formula); 
	print("done\n");
	println("Outcome is \'<solving.result.sat>\'");
	println("Solving time in Z3: <solving.time/1000000> ms");

	Model currentModel = ();
	Environment next() {
		currentModel = nextModel(solverPid, currentModel);
		if (currentModel == ()) {
			return ();
		} else {
			return merge(currentModel, translation.environment);
		}
	}

	if(solving.result.sat) {
		currentModel = firstModel(solverPid, vars);
		return sat(merge(currentModel, translation.environment), originalProblem.uni, next, stop);
	} else {
		return unsat(getUnsatCore(solverPid, solving.result.labels));
	}
}

Environment merge(Model model, Environment environment) 
	= visit(environment) {
		case var(str name) => model[name] ? \true() : \false() when name in model
	};

private tuple[&T, int] benchmark(&T () methodToBenchmark) {
	int startTime = userTime();
	&T result = methodToBenchmark();
	return <result, userTime() - startTime>;
}

private tuple[&T, int] benchmark(&T (&R) methodToBenchmark, &R p) {
	int startTime = userTime();
	&T result = methodToBenchmark(p);
	return <result, userTime() - startTime>;
}

private tuple[&T, int] benchmark(&T (&R,&Q) methodToBenchmark, &R p1, &Q p2) {
	int startTime = userTime();
	&T result = methodToBenchmark(p1,p2);
	return <result, userTime() - startTime>;
}

private tuple[&T, int] benchmark(&T (&R,&Q,&S) methodToBenchmark, &R p1, &Q p2, &S p3) {
	int startTime = userTime();
	&T result = methodToBenchmark(p1,p2,p3);
	return <result, userTime() - startTime>;
}



