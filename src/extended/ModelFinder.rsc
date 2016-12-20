module extended::ModelFinder

import logic::Integer;
import logic::Propositional;

import extended::SMTCompiler;

import extended::AST;
import extended::Translator;
import extended::SolverRunner;
import extended::Binder;

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
	print("Building initial environment maps...");
	tuple[Environment env, int time] ie = benchmark(createInitialEnvironment, problem);
	print("done, took: <(ie.time/1000000)> ms\n");
	
	print("Translating problem to SAT formula...");
	tuple[Formula formula, int time] t = benchmark(translateExtended, problem, ie.env);
	print("done, took: <(t.time/1000000)> ms\n");
	
	iprintln(t.formula);
	
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
	
	set[str] boolVars = {name | str relName <- env, Index idx  <- env[relName], var(str name) := env[relName][idx]};
	set[str] intVars = {name | str relName <- env, Index idx  <- env[relName], intVar(str name) := env[relName][idx]};
	
	print("Translating to SMT formulae...");
	tuple[str smt, int time] smtBoolVars = benchmark(compileDeclaredBoolVariables, boolVars);
	tuple[str smt, int time] smtIntVars = benchmark(compileDeclaredIntVariables, intVars);
	tuple[str smt, int time] smtForm = benchmark(compileAssertedFormula, formula);
	print("done, took: <(smtBoolVars.time + smtIntVars.time + smtForm.time) /1000000> ms\n");
	
	writeFile(|project://allealle/bin/test.smt|, smtBoolVars.smt + smtIntVars.smt + smtForm.smt);
		
	print("Solving by Z3...");
	tuple[bool result, int time] solving = benchmark(isSatisfiable, solverPid, smtBoolVars.smt + smtIntVars.smt + smtForm.smt); 
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
		currentModel = firstModel(solverPid, boolVars, intVars);
		return sat(merge(currentModel, env), originalProblem.uni, next, stop);
	} else {
		return unsat({});
	}
}

Environment merge(Model model, Environment environment) 
	= visit(environment) {
		case var(str name) => model[name] when name in model
		case intVar(str name) => model[name] when name in model
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


