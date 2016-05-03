module orig::SolverRunner

import smt::solver::Z3;
import orig::SMTCompiler;
import logic::Propositional;

import List;

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

tuple[bool sat, map[str, Formula] labels] isSatisfiable(SolverPID pid, set[str] vars, \and(set[Formula] clauses)) { 
	if ("" !:= runInSolver(pid, intercalate("\n", ["(declare-const <v> Bool)" | v <- vars]))) {
		throw "Unable to declare needed variables in SMT";
	}
	 
	SMTCompilerResult smtCompResult = compileToSMT(clauses);	 
	 
	if ("" !:= runInSolver(pid, smtCompResult.formula)) {
		throw "Unable to assert clauses"; 
	} 	
	
	return switch(runSolver(pid, "(check-sat)")) {
		case "sat" : return <true, smtCompResult.labels>;
		case "unsat": return <false, smtCompResult.labels>;
		case "unknown": throw "Could not compute satisfiability";		
	}
}

str getValues(SolverPID pid, set[str] vars) {
	resp = runSolver(pid, "(get-value (<intercalate(" ", [v | v <- vars])>)");
	if (resp != "") {
		return resp;
	}
	
	throw "Unable to get values for variables from solver";
}

list[str] getUnsatCore(SolverPID pid, map[str, Formula] labels) {
	resp = runSolver(pid, "(get-unsat-core)");
	
	if (resp != "") {
		return response;
	} 
	
	throw "Unable to get the unsatisfiable core";
}

private str runSolver(SolverPID pid, str commands) {
	try {
		return run(pid, commands, debug=true);
	}
	catch er: throw "Error while running SMT solver, reason: <er>"; 	
}
