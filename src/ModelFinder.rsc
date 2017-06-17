module ModelFinder

import logic::Propositional;
 
import theories::AST;
import theories::PreProcessor;
import theories::Translator; 
import theories::SMTInterface; 
import theories::Binder;
import theories::Unparser;

import smt::solver::SolverRunner; 

import util::Benchmark;
import IO; 
import List;
import String;
import Map;
import Set;
 
alias PID = int; 

data ModelFinderResult 
	= sat(Model currentModel, Universe universe, Model (Theory) nextModel, void () stop)
	| unsat(set[Formula] unsatCore)
	| trivialSat(Model model, Universe universe)
	| trivialUnsat()	
	;

ModelFinderResult checkInitialSolution(Problem problem) {
	print("Preprocessing problem (replacing constants, replacing expressions in different theories)...");
	tuple[Problem problem, int time] pp = benchmark(preprocess, problem);
	print("done, took: <(pp.time/1000000)> ms\n");
	
	Problem augmentedProblem = pp.problem;	
	
	writeFile(|project://allealle/examples/last_transformed.alle|, unparse(augmentedProblem));
	
	print("Building initial environment...");
	tuple[Environment env, int time] ie = benchmark(createInitialEnvironment, augmentedProblem); 
	print("done, took: <(ie.time/1000000)> ms\n");
	
 
	print("Translating problem to SAT formula...");
	tuple[Formula formula, int time] t = benchmark(translate, augmentedProblem, ie.env);
	print("done, took: <(t.time/1000000)> ms\n");
	 
	//print("Converting to CNF...");
	//tuple[Formula formula, int time] cnf = <t.result.formula, t.time>; //benchmark(convertToCNF, t.result.formula);

	if (t.formula == \false()) {
		return trivialUnsat();
	} else if (t.formula == \true()) {
		return trivialSat(empty(), problem.uni);
	}

	return runInSolver(augmentedProblem, t.formula, ie.env);
}

ModelFinderResult runInSolver(Problem problem, Formula formula, Environment env) {
	PID solverPid = startSolver();
	void stop() {
		stopSolver(solverPid);
	} 
	
	print("Translating to SMT-LIB...");
  tuple[set[SMTVar] vars, int time] smtVarCollectResult = benchmark(collectSMTVars, problem.uni, env);
	tuple[str smt, int time] smtVarDeclResult = benchmark(compileSMTVariableDeclarations, smtVarCollectResult.vars);
	tuple[str smt, int time] smtAtomDeclExprs = benchmark(compileAtomExpressions, problem.uni.atoms);
	tuple[str smt, int time] smtCompileFormResult = benchmark(compileAssert, formula);
	print("done, took: <(smtVarCollectResult.time + smtVarDeclResult.time + smtAtomDeclExprs.time + smtCompileFormResult.time) /1000000> ms in total (variable collection fase: <smtVarCollectResult.time / 1000000>, variable declaration fase: <smtVarDeclResult.time / 1000000>, atom expression translation fase: <smtAtomDeclExprs.time / 1000000>, formula compilation fase: <smtCompileFormResult.time / 1000000>\n");
	println("Total nr of clauses in formula: <countClauses(formula)>, total nr of variables in formula: <countVars(smtVarCollectResult.vars)>"); 
	
	writeFile(|project://allealle/bin/latestSmt.smt2|, "<smtVarDeclResult.smt>\n<smtAtomDeclExprs.smt>\n<smtCompileFormResult.smt>");
	  
	print("Solving by Z3...");
	tuple[bool result, int time] solving = benchmark(isSatisfiable, solverPid, "<smtVarDeclResult.smt>\n<smtAtomDeclExprs.smt>\n<smtCompileFormResult.smt>"); 
	print("done, took: <solving.time/1000000> ms\n");
	println("Outcome is \'<solving.result>\'");
 
	SMTModel smtModel = ();
	Model model = empty();
	
	Model next(Theory t) {
	  print("Getting next model from SMT solver...");
		smtModel = nextSmtModel(solverPid, model, t, smtVarCollectResult.vars);
	  print("done!\n");
	        
		if (smtModel == ()) {
			return empty();
		} else {
		  model = constructModel(smtModel, problem.uni, env);
			return model;
		}
	}  

	if(solving.result) {
		smtModel = firstSmtModel(solverPid, smtVarCollectResult.vars);
		model = constructModel(smtModel, problem.uni, env);
		
		return sat(model, problem.uni, next, stop);
	} else {
		return unsat({});
	}
}

SMTModel getValues(SolverPID pid, set[SMTVar] vars) {
  resp = runSolver(pid, "(get-value (<intercalate(" ", [v.name | v <- vars])>))", wait=50);
  return getValues(resp, vars);
}
 
SMTModel firstSmtModel(SolverPID pid, set[SMTVar] vars) = getValues(pid, vars);

SMTModel nextSmtModel(SolverPID pid, Model currentModel, Theory t, set[SMTVar] vars) { 
  Formula findCurrentSmtVal(SMTVar v) = \true() when Relation r <- currentModel.relations, vectorAndVar(list[Atom] _, str smtVarName)  <- r.relation, smtVarName == v.name;
  default Formula findCurrentSmtVal(SMTVar v) = \false();
  
  str smt = "";
   
  if (t == relTheory()) {
    smt = ("" | it + " <negateVariable(v.name, findCurrentSmtVal(v))>" | SMTVar v <- vars, v.theory == relTheory());
  } else {
    smt = ("" | it + " <negateAtomVariable(v)>" | v:varAtom(str _, Theory _, AtomValue _) <- currentModel.visibleAtoms); 
  } 
  
  println(smt); 
  
  if ("" !:= runSolver(pid, "(assert (or <smt>))")) {
    throw "Unable to declare needed variables in SMT";
  }   
  
  if (checkSat(pid)) {
    return getValues(pid, vars);
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



