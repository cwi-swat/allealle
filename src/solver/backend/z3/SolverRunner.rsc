module solver::backend::z3::SolverRunner

import solver::backend::z3::Z3;

import List;
import String;
import Boolean;
import IO;
import Map;

import util::Sleeper;

alias SolverPID = int;

SolverPID startSolver() {
	pid = startZ3();
	
	// make sure that the unsatisfiable core are produced
	runSolver(pid, "(set-option :produce-unsat-cores true)");
	
	return pid;
}

void stopSolver(SolverPID pid) {
	stopZ3(pid);
}

bool isSatisfiable(SolverPID pid, str smtFormula) { 
	if (smtFormula != "") {
    	list[str] smt = split("\n", smtFormula);
    	for (s <- smt) {
        str solverResult = trim(runSolver(pid, s)); 
    	  if (solverResult != "") {
    		  throw "Unable to assert clauses: <solverResult>"; 
    	  } 	
    	}
    	
    	// do a 'flush'
    	runSolver(pid, "\n");
  }
  
  return checkSat(pid);
}

bool checkSat(SolverPID pid) {
	str result = runSolverAndExpectResult(pid, "(check-sat)");
	
	println(result);
	
	switch(result) {
		case /unsat.*/: return false;
    case /sat.*/ : return true;
		case /unknown.*/: throw "Could not compute satisfiability";		
		default: throw "unable to get result from smt solver";
	}
}

int getSolvingTime(SolverPID pid) {
  str result = runSolverAndExpectResult(pid, "(get-info :all-statistics)");
  
  int time;  
  if (/[:]time[ ]*<sec:[0-9]*>[.]<hun:[0-9][0-9]>/ := result) {
    time = toInt(sec)*1000 + toInt(hun[0] == "0" ? hun[1] : hun)*10;  
  } else {
    throw "Unable to parse the solving time from the statistics of Z3";
  }
  
  return time;
}

str runSolverAndExpectResult(SolverPID pid, str commands) { 
  str result = run(pid,commands, debug=false);
  
  while (true) {
    try {
      str oldResult = result;
      sleep(5);
      result += read(pid);
      
      if(trim(result) != "" && result == oldResult) {
        return result;
      }
    } catch ex: {
      println("Exception while SMT solver, reason: <er>");
      println("Retrying...");
    }
  }
}

str runSolver(SolverPID pid, str commands) {
	try {
		return run(pid, commands, debug=false);
	}
	catch er: throw "Error while running SMT solver, reason: <er>"; 	
}
