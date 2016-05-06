module orig::SolverRunner

import smt::solver::Z3;
import orig::SMTCompiler;
import logic::Propositional;

import List;
import String;
import Boolean;
import IO;
import Map;

alias SolverPID = int;

alias CheckSatResult = tuple[bool sat, map[str, Formula] labels];

alias Model = map[str var, bool exists];

SolverPID startSolver() {
	pid = startZ3();
	
	// make sure that the unsatisfiable core are produced
	runSolver(pid, "(set-option :produce-unsat-cores true)");
	
	return pid;
}

void stopSolver(SolverPID pid) {
	stopZ3(pid);
}

CheckSatResult isSatisfiable(SolverPID pid, set[str] vars, Formula formula) { 
	if ("" !:= runSolver(pid, intercalate("\n", ["(declare-const <v> Bool)" | v <- vars]))) {
		throw "Unable to declare needed variables in SMT";
	}
	 
	SMTCompilerResult smtCompResult = compileToSMT(formula);	 
	 
	if ("" !:= runSolver(pid, smtCompResult.smtFormula)) {
		throw "Unable to assert clauses"; 
	} 	
	
	return checkSat(pid, smtCompResult.labels);
}

private CheckSatResult checkSat(SolverPID pid, map[str, Formula] labels) {
	switch(runSolver(pid, "(check-sat)")) {
		case "sat" : return <true, labels>;
		case "unsat": return <false, labels>;
		case "unknown": throw "Could not compute satisfiability";		
	}
}

private Model getValues(SolverPID pid, set[str] vars) {
	resp = runSolver(pid, "(get-value (<intercalate(" ", [v | v <- vars])>))");
	if (resp != "") {
		return (() | it + (var:fromString(val)) | /(<var:[A-Za-z_0-9]*> <val:false|true>)/ := substring(resp, 1, size(resp)-1));
	}
	
	throw "Unable to get values for variables from solver";
}

Model firstModel(SolverPID pid, set[str] vars) = getValues(pid, vars);

Model nextModel(SolverPID pid, Model currentModel) {
	if ("" !:= runSolver(pid, "(assert (or <intercalate(" ", [var | v <- currentModel, str var := (currentModel[v] ? "(not <v>)" : v)])>))")) {
		throw "Unable to declare needed variables in SMT";
	}		
	
	if (checkSat(pid, ()).sat) {
		return getValues(pid, domain(currentModel));
	} else {
		return ();
	}
}

set[Formula] getUnsatCore(SolverPID pid, map[str, Formula] labels) {
	resp = runSolver(pid, "(get-unsat-core)");
	
	if (resp != "") {
		set[str] keys = {s | str s <- split(" ", substring(resp,1,size(resp)-1))};
		return {labels[k] | k <- keys};
	} 
	
	throw "Unable to get the unsatisfiable core";
}

private str runSolver(SolverPID pid, str commands) {
	try {
		return run(pid, commands, debug=false);
	}
	catch er: throw "Error while running SMT solver, reason: <er>"; 	
}
