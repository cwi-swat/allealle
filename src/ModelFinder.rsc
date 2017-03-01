module ModelFinder

import logic::Propositional;
 
import theories::AST;
import theories::Translator; 
import theories::SMTInterface; 
import theories::Binder;
import smt::solver::SolverRunner; 

import util::Benchmark;
import IO; 
import List;
import String;
import Map;
import Set;
 
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

	//println("SAT Formula:");
	//iprintln(t.formula); 
	 
	//print("Converting to CNF...");
	//tuple[Formula formula, int time] cnf = <t.result.formula, t.time>; //benchmark(convertToCNF, t.result.formula);

	if (t.formula == \false()) {
		return trivial(false);
	} else if (t.formula == \true()) {
		return trivial(true);
	}

	return runInSolver(problem, t.formula, ie.env);
}

ModelFinderResult runInSolver(Problem originalProblem, Formula formula, Environment env) {
	PID solverPid = startSolver();
	void stop() {
		stopSolver(solverPid);
	}
	
	print("Translating to SMT-LIB...");
  tuple[set[SMTVar] vars, int time] smtVarCollectResult = benchmark(collectSMTVars, env);
	tuple[str smt, int time] smtVarDeclResult = benchmark(compileSMTVariableDeclarations, smtVarCollectResult.vars);
	tuple[str smt, int time] smtCompileFormResult = benchmark(compileAssert, formula);
	print("done, took: <(smtVarCollectResult.time + smtVarDeclResult.time + smtCompileFormResult.time) /1000000> ms in total (variable collection fase: <smtVarCollectResult.time / 1000000>, variable declaration fase: <smtVarDeclResult.time / 1000000>, formula compilation fase: <smtCompileFormResult.time / 1000000>\n");
	println("Total nr of clauses in formula: <countClauses(formula)>, total nr of variables in formula: <countVars(smtVarCollectResult.vars)>"); 
	
	writeFile(|project://allealle/bin/latestSmt.smt|, "<smtVarDeclResult.smt>\n<smtCompileFormResult.smt>");
	
	print("Solving by Z3...");
	tuple[bool result, int time] solving = benchmark(isSatisfiable, solverPid, "<smtVarDeclResult.smt>\n<smtCompileFormResult.smt>"); 
	print("done, took: <solving.time/1000000> ms\n");
	println("Outcome is \'<solving.result>\'");
 
	Model currentModel = ();
	Environment next() {
		currentModel = nextModel(solverPid, currentModel);
	  
	  println("Next model is:");
  
		if (currentModel == ()) {
			return ();
		} else {
			return merge(currentModel, env);
		}
	}

	if(solving.result) {
		currentModel = firstModel(solverPid, smtVarCollectResult.vars);
		
		return sat(merge(currentModel, env), originalProblem.uni, next, stop);
	} else {
		return unsat({});
	}
}

Model getValues(SolverPID pid, set[SMTVar] vars) {
  resp = runSolver(pid, "(get-value (<intercalate(" ", [v.name | v <- vars])>))");
  return getValues(resp, vars);
}
 
Model firstModel(SolverPID pid, set[SMTVar] vars) = getValues(pid, vars);

Model nextModel(SolverPID pid, Model currentModel) {
  str smt = "";
  
  for (SMTVar var <- currentModel, str cur := negateVariable(var, currentModel[var]), cur != "") {
    smt += " <cur>";
  }
  
  if ("" !:= runSolver(pid, "(assert (or <smt>))")) {
    throw "Unable to declare needed variables in SMT";
  }   
  
  if (checkSat(pid)) {
    return getValues(pid, domain(currentModel));
  } else {
    return ();
  }
}

private int countClauses(Formula f) {
  int nrOfClauses = 0;
  visit(f) {
    case Formula _ : nrOfClauses += 1;
  }
  
  return nrOfClauses;
}

private int countVars(set[SMTVar] vars) = size(vars);

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



