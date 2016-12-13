module orig::ModelFinder

import logic::Propositional;

import orig::AST;
import orig::Imploder;
import orig::FormulaTranslator;
import orig::SMTCompiler;
import logic::CNFConverter;
import orig::SolverRunner;
import orig::ExpressionTranslator;

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
	print("Building initial environment...");
	tuple[Environment env, int time] ie = benchmark(createInitialEnvironment, problem);
	print("done, took: <(ie.time/1000000)> ms\n");
	
	print("Translating problem to SAT formula...");
	tuple[Formula formula, int time] t = benchmark(translate, problem, ie.env);
	print("done, took: <(t.time/1000000)> ms\n");
	
	//iprintln(t.formula);
	
	//println("SAT Formula:");
	//iprintln(t.result.formula); 
	 
	//print("Converting to CNF...");
	//tuple[Formula formula, int time] cnf = <t.result.formula, t.time>; //benchmark(convertToCNF, t.result.formula);

	if (t.formula == \false()) {
		return trivial(false);
	} else if (t.formula == \true()) {
		return trivial(true);
	}

	return runInSolver(problem, t.formula, ie.env);
}

private ModelFinderResult runInSolver(Problem originalProblem, Formula formula, Environment env) {
	PID solverPid = startSolver();
	void stop() {
		stopSolver(solverPid);
	}
	
	set[str] vars = {name | str relName <- env, Index idx  <- env[relName], var(str name) := env[relName][idx]};
	
	print("Translating to SMT-LIB...");
	tuple[str smt, int time] smtVars = benchmark(compileDeclaredVariables, vars);
	tuple[str smt, int time] smtForm = benchmark(compileAssertedFormula, formula);
	print("done, took: <(smtVars.time + smtForm.time) /1000000> ms\n");
	
	print("Solving by Z3...");
	tuple[bool result, int time] solving = benchmark(isSatisfiable, solverPid, smtVars.smt + smtForm.smt); 
	print("done, took: <solving.time/1000000> ms\n");
	println("Outcome is \'<solving.result>\'");

	Model currentModel = ();
	Environment next() {
		currentModel = nextModel(solverPid, currentModel);
		if (currentModel == ()) {
			return ();
		} else {
			return merge(currentModel, env);
		}
	}

	if(solving.result) {
		currentModel = firstModel(solverPid, vars);
		return sat(merge(currentModel, env), originalProblem.uni, next, stop);
	} else {
		return unsat({});
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



