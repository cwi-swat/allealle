module solver::backend::z3::SolverRunner

import solver::backend::z3::Z3;

import List;
import String;
import Boolean;
import IO;
import Map;

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
    	runSolver(pid, "", wait=5);
  }
  	
	bool gotAnswer = false;
	while (!gotAnswer) {
	  try {
      println("Starting to check satisfiability");
	    bool sat = checkSat(pid);
	    gotAnswer = true;
	    return sat;
    } catch ex: {
      println("Exception while checking satisfiability: <ex>");
      println("Retrying...");
    }
  }
}

bool checkSat(SolverPID pid) {
	str result = runSolver(pid, "(check-sat)", wait=5);
	
	println(result);
	
	switch(result) {
		case /unsat.*/: return false;
    case /sat.*/ : return true;
		case /unknown.*/: throw "Could not compute satisfiability";		
		default: throw "unable to get result from smt solver";
	}
}

int getSolvingTime(SolverPID pid) {
  str result = runSolver(pid, "(get-info :all-statistics)", wait=5);
  
  int time;  
  if (/[:]time[ ]*<sec:[0-9]*>[.]<hun:[0-9][0-9]>/ := result) {
    time = toInt(sec)*1000 + toInt(hun[0] == "0" ? hun[1] : hun)*10;  
  } else {
    throw "Unable to parse the solving time from the statistics of Z3";
  }
  
  return time;
}

str runSolver(SolverPID pid, str commands, int wait = 0) {
	try {
		return run(pid, commands, debug=false, wait = wait);
	}
	catch er: throw "Error while running SMT solver, reason: <er>"; 	
}
