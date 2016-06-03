module extended::SolverRunner

extend smt::solver::SolverRunner;

import logic::Propositional;

import String;
import Set;

data ModelValue
	= val(bool exists)
	| val(bool exists, int i)
	;

alias Model = map[str, ModelValue];

Model getValues(SolverPID pid, set[str] boolVars, set[str] intVars) {
	Model m = ();

	if (size(intVars) > 0) {
		resp = runSolver(pid, "(get-value (<("" | "<it> <v>_int" | v <- intVars)>))");
		
		if (resp != "") {
			m = (var:val(false, toInt(v)) | /(<var:[A-Za-z_0-9]*>_int <v:[0-9]+>)/ := substring(resp, 1, size(resp)-1));	
		}
	}

	str resp = runSolver(pid, "(get-value (<("" | "<it> <v>" | v <- boolVars)>))");
	if (resp != "") {
		 m = (var:val(fromString(v), m[var].i) | /(<var:[A-Za-z_0-9]*> <v:false|true>)/ := substring(resp, 1, size(resp)-1), var in m) +
		 	 (var:val(fromString(v)) | /(<var:[A-Za-z_0-9]*> <v:false|true>)/ := substring(resp, 1, size(resp)-1), var notin m);
	}
	
	return m;
}

Model firstModel(SolverPID pid, set[str] boolVars, set[str] intVars) = getValues(pid, boolVars, intVars);

Model nextModel(SolverPID pid, Model currentModel) {
	if ("" !:= runSolver(pid, "(assert (or <intercalate(" ", [var | v <- currentModel, str var := (currentModel[v].exists ? "(not <v>)" : v)])>))")) {
		throw "Unable to declare needed variables in SMT";
	}		
	
	if (checkSat(pid)) {
		return getValues(pid, getBoolVars(currentModel), getIntVars(currentModel));
	} else {
		return ();
	}
}

private set[str] getBoolVars(Model m) = {n | str n <- m};
private set[str] getIntVars(Model m) = {n | str n <- m, val(_, int _) := m[n]};
