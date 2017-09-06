module ModelFinder

import logic::Propositional;
 
import translation::AST;
import translation::Translator; 
import translation::SMTInterface; 
import translation::Binder;
import translation::Unparser;

import smt::solver::SolverRunner; 

import util::Benchmark;
import IO; 
import List;
import String;
import Map;
import Set;
 
alias PID = int; 

data ModelFinderResult 
	= sat(Model currentModel, Model (Domain) nextModel, void () stop)
	| unsat(set[Formula] unsatCore)
	| trivialSat(Model model)
	| trivialUnsat()	
	;

ModelFinderResult checkInitialSolution(Problem problem) {	
	print("Building initial environment...");
	tuple[Environment env, int time] ie = bm(createInitialEnvironment, problem); 
	print("done, took: <(ie.time/1000000)> ms\n");
	
 
	println("Translating problem to SAT formula...");
	tuple[TranslationResult r, int time] t = bm(translateProblem, problem, ie.env);
	println("\n\nDone translating, took: <(t.time/1000000)> ms");
	 
	if (t.r.relationalFormula == \false()) {
		return trivialUnsat();
	} else if (t.r.relationalFormula == \true()) {
		return trivialSat(empty());
	} 

	return runInSolver(problem, t.r, ie.env); 
}

ModelFinderResult runInSolver(Problem problem, TranslationResult tr, Environment env) {
	PID solverPid = startSolver(); 
	void stop() {
		stopSolver(solverPid);
	} 
	
	print("Translating to SMT-LIB...");
  tuple[set[SMTVar] vars, int time] smtVarCollectResult = bm(collectSMTVars, env);
  tuple[set[SMTVar] tmpVars, int time] smtTmpVarCollectResult = bm(collectIntermediateSMTVars, tr.intermediateVars);
	tuple[str smt, int time] smtVarDeclResult = bm(compileSMTVariableDeclarations, smtVarCollectResult.vars + smtTmpVarCollectResult.tmpVars);
	tuple[str smt, int time] smtCompileRelFormResult = bm(compileAssert, tr.relationalFormula);
	tuple[str smt, int time] smtCompileAttFormResult = bm(compileAssert, tr.attributeFormula);
	tuple[str smt, int time] smtCompileAdditionalComands = bm(compileAdditionalCommands, tr.additionalCommands);
	
	print("done, took: <(smtVarCollectResult.time + smtTmpVarCollectResult.time + smtVarDeclResult.time + smtCompileRelFormResult.time + smtCompileAttFormResult.time + smtCompileAdditionalComands.time) /1000000> ms in total (variable collection fase: <smtVarCollectResult.time / 1000000>, intermediate variable collection fase: <smtTmpVarCollectResult.time / 1000000>, variable declaration fase: <smtVarDeclResult.time / 1000000>, relational formula compilation fase: <smtCompileRelFormResult.time / 1000000>, attribute formula compilation phase: <smtCompileAttFormResult.time / 1000000>, additional command compilation phase: <smtCompileAdditionalComands.time / 1000000>\n");
  println("Total nr of clauses in formula: <countClauses(\and(tr.relationalFormula, tr.attributeFormula))>, total nr of variables in formula: <countVars(smtVarCollectResult.vars)>"); 
	
	str fullSmtProblem = "<smtVarDeclResult.smt>\n<smtCompileRelFormResult.smt>\n<smtCompileAttFormResult.smt>\n<smtCompileAdditionalComands.smt>";
	
	writeFile(|project://allealle/bin/latestSmt.smt2|, "<fullSmtProblem>\n(check-sat)");
	  
	print("Solving by Z3...");
	tuple[bool result, int time] solving = bm(isSatisfiable, solverPid, fullSmtProblem); 
	print("done, took: <solving.time/1000000> ms\n");
	println("Outcome is \'<solving.result>\'");
 
	SMTModel smtModel = ();
	Model model = empty();
	
	Model next(Domain dom) {
	  print("Getting next model from SMT solver...");
		smtModel = nextSmtModel(solverPid, dom, smtModel, model, smtVarCollectResult.vars);
	  print("done!\n");
	        
		if (smtModel == ()) {
			return empty();
		} else {
		  model = constructRelationalModel(smtModel, env);
			return model;
		}
	}  

	if(solving.result) {
		smtModel = firstSmtModel(solverPid, smtVarCollectResult.vars);
		model = constructRelationalModel(smtModel, env);
		
		return sat(model, next, stop);
	} else { 
		return unsat({});
	}
}

SMTModel getValues(SolverPID pid, set[SMTVar] vars) {
  resp = runSolver(pid, "(get-value (<intercalate(" ", [v.name | v <- vars])>))", wait=50);
  
  return getValues(resp, vars);
}
 
SMTModel firstSmtModel(SolverPID pid, set[SMTVar] vars) = getValues(pid, vars);

SMTModel nextSmtModel(SolverPID pid, Domain dom, SMTModel currentSmtModel, Model currentRelationalModel, set[SMTVar] vars) { //Model currentRelationalModel, Domain dom, set[SMTVar] vars) { 
  str smt = "";
   
  if (dom == id()) {
    smt = ("" | it + " <negateVariable(name, currentSmtModel[v])>" | v:<str name, id()> <- currentSmtModel);
  } 
  else {
    smt = ("" | it + " <negateAttribute(dom, smtVarName, val)>" | ModelRelation r <- currentRelationalModel.relations, ModelTuple t <- r.tuples, varAttribute(str _, dom, Value val, str smtVarName) <- t.attributes); 
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

private tuple[&T, int] bm(&T () methodToBenchmark) {
	int startTime = userTime();
	&T result = methodToBenchmark();
	return <result, userTime() - startTime>;
}

private tuple[&T, int] bm(&T (&R) methodToBenchmark, &R p) {
	int startTime = userTime();
	&T result = methodToBenchmark(p);
	return <result, userTime() - startTime>;
}

private tuple[&T, int] bm(&T (&R,&Q) methodToBenchmark, &R p1, &Q p2) {
	int startTime = userTime();
	&T result = methodToBenchmark(p1,p2);
	return <result, userTime() - startTime>;
}

private tuple[&T, int] bm(&T (&R,&Q,&S) methodToBenchmark, &R p1, &Q p2, &S p3) {
	int startTime = userTime();
	&T result = methodToBenchmark(p1,p2,p3);
	return <result, userTime() - startTime>;
}



