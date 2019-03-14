module ModelFinder

import smtlogic::Core;
 
import translation::AST;
import translation::Relation;
import translation::Environment;
import translation::Translator; 
import translation::SMTInterface; 
import translation::Unparser;

import solver::backend::z3::SolverRunner; 

import util::Benchmark;
import util::MemoCacheClearer;
import IO; 
import ValueIO;
import List;
import String;
import Map;
import Set;
 
alias PID = int; 

data ModelFinderResult(int translationTime = -1, int solvingTime = -1) 
	= sat(Model currentModel, Model (Domain) nextModel, void () stop)
	| unsat(set[Formula] unsatCore)
	| trivialSat(Model model)
	| trivialUnsat()	
	| timeout()
	| unknown()
	;

ModelFinderResult checkInitialSolution(Problem problem, int timeOutInMs = 0) {	
	print("Building initial environment...");
	tuple[Environment env, int time] ie = bm(createInitialEnvironment, problem); 
	print("done, took: <(ie.time/1000000)> ms\n");
 
	println("Translating problem to SMT formula...");
	tuple[TranslationResult tr, int time] t = bm(translateProblem, problem, ie.env);
	println("\n\nDone translating, took: <(t.time/1000000)> ms");
	
	//countDeepestNesting(t.r.relationalFormula);
	
	int totalTime = (ie.time + t.time) / 1000000;
	 
	if (t.tr.form == \false()) {
		return trivialUnsat(translationTime=totalTime);
	} else if (t.tr.form == \true()) {
		return trivialSat(empty(),translationTime=totalTime);
	} 
 
	return runInSolver(problem, t.tr, ie.env, totalTime, timeOutInMs); 
}


ModelFinderResult runInSolver(Problem problem, TranslationResult tr, Environment env, int translationTime, int timeOutInMs) {
	PID solverPid = startSolver();
	if (timeOutInMs != 0) {
	   setTimeOut(solverPid, timeOutInMs);
	} 
	
  void stop() {
		stopSolver(solverPid);
	} 
	
	print("Translating to SMT-LIB...");
  tuple[set[SMTVar] vars, int time] smtVarCollectResult = bm(collectSMTVars, env);
	tuple[str smt, int time] smtVarDeclResult = bm(compileSMTVariableDeclarations, smtVarCollectResult.vars);
	tuple[str smt, int time] smtCompileFormResult = bm(compileAssert, tr.form);
	tuple[str smt, int time] smtCompileCommands = bm(compileCommands, tr.cmds);
	
	print("done, took: <(smtVarCollectResult.time + smtVarDeclResult.time + smtCompileFormResult.time + smtCompileCommands.time) /1000000> ms in total (variable collection fase: <smtVarCollectResult.time / 1000000>, variable declaration fase: <smtVarDeclResult.time / 1000000>, formula compilation fase: <smtCompileFormResult.time / 1000000>, commands compilation fase: <smtCompileCommands.time / 1000000>)\n");
  //println("Total nr of clauses in formula: <countClauses(\and(tr.relationalFormula, tr.attributeFormula))>, total nr of variables in formula: <countVars(smtVarCollectResult.vars)>"); 
	
	str preambl = intercalate("\n", [pa | Sort s <- collectSorts(smtVarCollectResult.vars), str pa := preamble(s), pa != ""]);
	
	str fullSmtProblem = preambl + "\n" + smtVarDeclResult.smt + "\n" + smtCompileFormResult.smt + "\n" + smtCompileCommands.smt;
	
	writeFile(|project://allealle/bin/latestSmt.smt2|, fullSmtProblem + "\n(check-sat)");
	
	SMTModel smtModel = ();
  Model model = empty();

  Model next(Domain dom) {
    print("Getting next model from SMT solver...");
    smtModel = nextSmtModel(solverPid, dom, smtModel, model, smtVarCollectResult.vars);
    print("done, took: <getSolvingTime(solverPid)> ms\n");
          
    if (smtModel == ()) {
      return empty();
    } else {
      model = constructRelationalModel(smtModel, env);
      return model;
    }
  }  
	  
	print("Solving by Z3...");
	try {
	  bool satisfiable = isSatisfiable(solverPid, fullSmtProblem);
	  int solvingTime = getSolvingTime(solverPid);
    print("done, took: <solvingTime> ms\n");
    println("Outcome is \'<satisfiable>\'");

    if(satisfiable) {
      smtModel = firstSmtModel(solverPid, smtVarCollectResult.vars);
      model = constructRelationalModel(smtModel, env);
      
      return sat(model, next, stop, translationTime = translationTime, solvingTime = solvingTime);
    } else { 
      stopSolver(solverPid);
      return unsat({}, translationTime = translationTime, solvingTime = solvingTime);
    }
    
	} catch ResultUnkownException ex: {
      int solvingTime = getSolvingTime(solverPid);
      stopSolver(solverPid);
      return (ex == to()) ? timeout(translationTime = translationTime, solvingTime = solvingTime) : unknown(translationTime = translationTime, solvingTime = solvingTime);
	}  
}

void countDeepestNesting(Formula f) {
  int recurse(\or(set[Formula] clauses), int level) = (level | found > it ? found : it | c <- clauses, int found := recurse(c, level+1)); 
  int recurse(\and(set[Formula] clauses), int level) = (level | found > it ? found : it | c <- clauses, int found := recurse(c, level+1)); 
  int recurse(\not(Formula f), int level) = recurse(f, level + 1); 
  default int recurse(Formula f, int level) = level;
  
  println("Deepest nesting = <recurse(f, 0)>");
}

SMTModel getValues(SolverPID pid, set[SMTVar] vars) {
  resp = runSolverAndExpectResult(pid, "(get-value (<intercalate(" ", [v.name | v <- vars])>))");
  
  return getValues(resp, vars);
}
 
SMTModel firstSmtModel(SolverPID pid, set[SMTVar] vars) = getValues(pid, vars);

SMTModel nextSmtModel(SolverPID pid, Domain dom, SMTModel currentSmtModel, Model currentRelationalModel, set[SMTVar] vars) { //Model currentRelationalModel, Domain dom, set[SMTVar] vars) { 
  Sort srt = domain2Sort(dom);
  str smt = "";

  if (srt == \bool()) {
    // If we want to get a new relational model we have to look at the current values of all the relational (boolean) variables
    smt = ("" | it + " <negateVariable(name, currentSmtModel[v])>" | SMTVar v:<str name, srt> <- currentSmtModel);
  } else {
    // If we want to get a new model for another theory we should only look at tuples which are currently visible and negate the attributes in those tuples of the given sort 
    for (ModelRelation r <- currentRelationalModel.relations, ModelTuple t <- r.tuples, varAttribute(str attName, Term val, str smtVarName) <- t.attributes) {
      smt += " <negateVariable(smtVarName, val)>";
    }
  }
   
  if (smt == "") {
    // No variables to negate so the presented model is the only possible model
    return ();
  }
  
  if ("" !:= runSolver(pid, "(assert (or <smt>))")) {
    throw "Unable to declare needed variables in SMT";
  }   
  
  if (isSatisfiable(pid,"")) {
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
	int startTime = cpuTime();
	&T result = methodToBenchmark();
	return <result, cpuTime() - startTime>;
}

private tuple[&T, int] bm(&T (&R) methodToBenchmark, &R p) {
	int startTime = cpuTime();
	&T result = methodToBenchmark(p);
	return <result, cpuTime() - startTime>;
}

private tuple[&T, int] bm(&T (&R,&Q) methodToBenchmark, &R p1, &Q p2) {
	int startTime = cpuTime();
	&T result = methodToBenchmark(p1,p2);
	return <result, cpuTime() - startTime>;
}

private tuple[&T, int] bm(&T (&R,&Q,&S) methodToBenchmark, &R p1, &Q p2, &S p3) {
	int startTime = cpuTime();
	&T result = methodToBenchmark(p1,p2,p3);
	return <result, cpuTime() - startTime>;
}



