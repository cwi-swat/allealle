module SolverRunner

extend smt::solver::SolverRunner;

import SMTCompiler; 

import logic::Propositional;

alias Model = map[str var, bool exists];

Model getValues(SolverPID pid, set[str] vars) {
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
	
	if (checkSat(pid)) {
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
