module ModelFinder

import logic::Propositional;
 
import AST;
import Translator;
import SMTInterface; 
import Binder;
import smt::solver::SolverRunner; 

import util::Benchmark;
import IO;
import List;
import String;
import Map;
 
alias PID = int;

data ModelFinderResult 
	= sat(Environment currentModel, Universe universe, Environment () nextModel, void () stop)
	| unsat(set[Formula] unsatCore)
	| trivial(bool sat)
	;

alias TranslationUnit = tuple[Translator translator, SMTInterface smtInterface]; 

list[Translator] getTranslators(list[TranslationUnit] tus) = [t.translator | TranslationUnit t <- tus];
list[SMTInterface] getSMTInterfaces(list[TranslationUnit] tus) = [t.smtInterface | TranslationUnit t <- tus]; 
list[SMTInterpreter] getSMTInterpreters(list[SMTInterface] apis) = [a.interpreter | SMTInterface a <- apis];

ModelFinderResult checkInitialSolution(Problem problem, list[TranslationUnit] translationUnits) {
	print("Building initial environment...");
	tuple[Environment env, int time] ie = benchmark(createInitialEnvironment, problem, getTranslators(translationUnits));
	print("done, took: <(ie.time/1000000)> ms\n");
	
	iprintln(ie.env);
	
	print("Translating problem to SAT formula...");
	tuple[Formula formula, int time] t = benchmark(translate, problem, ie.env, getTranslators(translationUnits));
	print("done, took: <(t.time/1000000)> ms\n");
	

	println("SAT Formula:");
	iprintln(t.formula); 
	 
	//print("Converting to CNF...");
	//tuple[Formula formula, int time] cnf = <t.result.formula, t.time>; //benchmark(convertToCNF, t.result.formula);

	if (t.formula == \false()) {
		return trivial(false);
	} else if (t.formula == \true()) {
		return trivial(true);
	}

	return runInSolver(problem, t.formula, ie.env, getSMTInterfaces(translationUnits));
}

private ModelFinderResult runInSolver(Problem originalProblem, Formula formula, Environment env, list[SMTInterface] interfaces) {
	PID solverPid = startSolver();
	void stop() {
		stopSolver(solverPid);
	}
	
	set[SMTVar] vars = ({} | it + v | SMTInterface i <- interfaces, set[SMTVar] v := i.collectVars(env));
	
	str compileVariableDeclarations(set[SMTVar] vars) {
	  str result = "";
	  
	  for (SMTVar var <- vars) {
      str compilerResult = "";
      bool alreadyCompiled = false;
            
	    for (SMTInterface interface <- interfaces) {
	      compilerResult = interface.compiler.declareVariable(var);
	      if (alreadyCompiled && compilerResult != "") {
	       throw "SMT Compilation error, more then two configured compilers compiled the same variable \'<var>\'";
	      }
	      result += "<compilerResult>";
	      compilerResult = "";
	      alreadyCompile = true;
	    }
	  }
	  
	  return result;	   
	}
	
  str compileAssertedFormula(Formula formula) {
    str result = "";
    
    for (SMTInterface interface <- interfaces, str smt := interface.compiler.compile(formula, compileFormula), smt != "") {
      if (result != "") {
        throw "SMT Compilation error, more then two configured compilers compiled the same asserted formula";
      }
      
      result = "(assert <smt>)"; 
    } 
    
    return result;
  }

	str compileFormula(Formula formula) {
	  str result = "";
	  
	  for (SMTInterface interface <- interfaces, str smt := interface.compiler.compile(formula, compileFormula), smt != "") {
      if (result != "") {
        throw "SMT Compilation error, more then two configured compilers compiled the same formula";
      }

      result = smt;
	  } 
	  
	  return result;
	}
	
	print("Translating to SMT-LIB...");
	tuple[str smt, int time] smtVars = benchmark(compileVariableDeclarations, vars);
	tuple[str smt, int time] smtForm = benchmark(compileAssertedFormula, formula);
	print("done, took: <(smtVars.time + smtForm.time) /1000000> ms\n");
	
	writeFile(|project://allealle/bin/latestSmt.smt|, "<smtVars.smt>\n<smtForm.smt>");
	
	print("Solving by Z3...");
	tuple[bool result, int time] solving = benchmark(isSatisfiable, solverPid, smtVars.smt + smtForm.smt); 
	print("done, took: <solving.time/1000000> ms\n");
	println("Outcome is \'<solving.result>\'");
 
  list[SMTInterpreter] interpreters = getSMTInterpreters(interfaces);
 
	Model currentModel = ();
	Environment next() {
		currentModel = nextModel(solverPid, currentModel, interpreters);
	  
	  println("Next model is:");
    iprintln(currentModel);
  
		if (currentModel == ()) {
			return ();
		} else {
			return merge(currentModel, env, interpreters);
		}
	}

	if(solving.result) {
		currentModel = firstModel(solverPid, vars, interpreters);
		
		println("Found model is:");
		iprintln(currentModel);
		
		return sat(merge(currentModel, env, interpreters), originalProblem.uni, next, stop);
	} else {
		return unsat({});
	}
}

Environment merge(Model model, Environment environment, list[SMTInterpreter] interpreters) =
  (environment | interpreter.merge(model, it) | SMTInterpreter interpreter <- interpreters); 

Model getValues(SolverPID pid, set[SMTVar] vars, list[SMTInterpreter] interpreters) {
  resp = runSolver(pid, "(get-value (<intercalate(" ", [v.name | v <- vars])>))");
  
  if (resp != "") {
    map[str,str] foundValues = (() | it + (var:val) | /(<var:[A-Za-z_0-9]+> <val:[^(^)]+>)/ := substring(resp, 1, size(resp)-1));
  
    return (() | it + interpreter.getValues(foundValues, vars) | SMTInterpreter interpreter <- interpreters); 
  }
  
  throw "Unable to get values for variables from solver";
}
 
Model firstModel(SolverPID pid, set[SMTVar] vars, list[SMTInterpreter] interpreters) = getValues(pid, vars, interpreters);

Model nextModel(SolverPID pid, Model currentModel, list[SMTInterpreter] interpreters) {
  str smt = "";
  
  for (SMTVar var <- currentModel, SMTInterpreter interpreter <- interpreters, str cur := interpreter.variableNegator(var, currentModel), cur != "") {
    smt += " <cur>";
  }
  
  if ("" !:= runSolver(pid, "(assert (or <smt>))")) {
    throw "Unable to declare needed variables in SMT";
  }   
  
  if (checkSat(pid)) {
    return getValues(pid, domain(currentModel), interpreters);
  } else {
    return ();
  }
}

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



