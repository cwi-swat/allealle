module extended::SolverRunner

extend smt::solver::SolverRunner;

import logic::Propositional;

data ModelValue
	= noVal()
	| intVal(int i)
	;
	
alias 

alias Model = map[str var, bool exists, WrappedValue val];

Model getValues(SolverPID pid, set[str] vars) {
	resp = runSolver(pid, "(get-value (<("" | "<it> (boolVal <v>)" | v <- vars)>))");
	
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
