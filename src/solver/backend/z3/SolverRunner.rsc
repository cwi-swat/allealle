module solver::backend::z3::SolverRunner

import solver::backend::z3::Z3;

import List;
import String;
import Boolean;
import IO;
import Map;

import util::Sleeper;

alias SolverPID = int;

data ResultUnkownException
  = to() // timeout
  | uk(str reason) // unknown
  ;

SolverPID startSolver() {
	pid = startZ3();
	
	// make sure that the unsatisfiable core are produced
	//runSolver(pid, "(set-option :produce-unsat-cores true)");
	
	return pid;
}

void stopSolver(SolverPID pid) {
	stopZ3(pid);
}

void setTimeOut(SolverPID pid, int timeOutInMs) {
  runSolver(pid, "(set-option :timeout <timeOutInMs>)");
}

bool isSatisfiable(SolverPID pid, str smtFormula, str checkCommand = "(check-sat)") { 
	//if (smtFormula != "") {
 //   	list[str] smt = split("\n", smtFormula);
 //   	for (s <- smt) {
 //       str solverResult = trim(runSolver(pid, s)); 
 //   	  if (solverResult != "") {
 //   		  throw "Unable to assert clauses: <solverResult>"; 
 //   	  } 	
 //   	}
 //   	
 //   	// do a 'flush'
 //   	runSolver(pid, "\n");
 // }
  str result = runSolver(pid, smtFormula);
  // do a 'flush'
  result += runSolver(pid, "\n");
  if (result != "") {
    // somethings wrong
    throw getReason(pid);
  }
  
  return checkSat(pid, checkCommand = checkCommand);
}

bool checkSat(SolverPID pid, str checkCommand = "(check-sat)") {
	str result = runSolverAndExpectResult(pid, checkCommand);
		
	switch(result) {
		case /unsat.*/: return false;
    case /sat.*/ : return true;
		case /unknown.*/: { throw getReason(pid);}		
		case /.*canceled.*/: { throw to(); }
		default: throw "unable to get result from smt solver. Result was: <result>"; 
	}
}

private ResultUnkownException getReason(SolverPID pid){
  str reason = runSolverAndExpectResult(pid, "(get-info :reason-unknown)");
  
  if (/.*canceled.*/ := reason || /.*timeout.*/ := reason || /.*resource[ ]limits[ ]reached.*/ := reason) {
    return to();
  } else {
    return uk(reason);
  }  
}

int getSolvingTime(SolverPID pid) {
  str result = runSolverAndExpectResult(pid, "(get-info :all-statistics)");
  
  int time;  
  if (/[:]time[ ]*<sec:[0-9]*>[.]<hun:[0-9][0-9]>/ := result) {
    time = toInt(sec)*1000 + toInt(hun[0] == "0" ? hun[1] : hun)*10;  
  } else {
    time = -1;
  }
  
  return time;
}

str runSolverAndExpectResult(SolverPID pid, str commands, int waitTime = 5) { 

  str result = run(pid,commands, debug=false);
  
  while (true) {
    try {
      str oldResult = result;
      sleep(waitTime); 
      result += read(pid);
      
      if(trim(result) != "" && result == oldResult) {
        return result;
      }
    } catch ex: {
      println("Exception while SMT solver, reason: <ex>");
      println("Retrying...");
    }
  }
}

str getValues(SolverPID pid, set[str] vars, int waitTime = 1) {
  int openBrackets = 0;
  bool inStringLit = false;
  
  void scan(str input) {
    int lastChar = -1;
    for (int c <- chars(input)) {
      switch (<c,inStringLit,lastChar>) {
        case <40,false,_>: openBrackets += 1; // open bracket
        case <41,false,_>: openBrackets -= 1; // close bracket
        case <34,false,_>: inStringLit = true;
        case <34,true,92>: ; // escaped quote
        case <34,true,_>: inStringLit = false; 
      }

      lastChar = c;
    }
    
  }
  
  str command = "(get-value (<intercalate(" ", [var | var <- vars])>))";
  str result = runSolverAndExpectResult(pid, command, waitTime = waitTime);
  scan(result);

  while (openBrackets != 0) {
    try {      
      sleep(waitTime); 
      
      str newResult = read(pid);
      scan(newResult);
      result += newResult;
      
    } catch ex: {
      println("Exception while SMT solver, reason: <ex>");
      println("Retrying...");
    }    
  }  
  
  return result;
}

str runSolver(SolverPID pid, str commands) {
	try {
		return run(pid, commands, debug=false);
	}
	catch er: throw "Error while running SMT solver, reason: <er>"; 	
}
