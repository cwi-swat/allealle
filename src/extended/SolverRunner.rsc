module extended::SolverRunner

extend smt::solver::SolverRunner;

import logic::Propositional;
import logic::Integer;

import String;
import Set;

alias Model = map[str, Formula];

Model getValues(SolverPID pid, set[str] boolVars, set[str] intVars) {
	Model m = ();

	if (size(intVars) > 0) {
		resp = runSolver(pid, "(get-value (<("" | "<it> <v>_int" | v <- intVars)>))");
		
		if (resp != "") {
			m = (var:\int(toInt(v)) | /(<var:[A-Za-z_0-9]*>_int <v:[0-9]+>)/ := substring(resp, 1, size(resp)-1));	
		}
	}

	str resp = runSolver(pid, "(get-value (<("" | "<it> <v>" | v <- boolVars)>))");
	if (resp != "") {
		 m += (var:toForm(v) | /(<var:[A-Za-z_0-9]*> <v:false|true>)/ := substring(resp, 1, size(resp)-1));
	}

	return m;
}

private Formula toForm("true") = \true();
private Formula toForm("false") = \false();

Model firstModel(SolverPID pid, set[str] boolVars, set[str] intVars) = getValues(pid, boolVars, intVars);

Model nextModel(SolverPID pid, Model currentModel) {
	if ("" !:= runSolver(pid, "(assert (or <intercalate(" ", [var | v <- currentModel, isRelVar(currentModel[v]), str var := ((\true() := currentModel[v]) ? "(not <v>)" : v)])>))")) {
		throw "Unable to declare needed variables in SMT";
	}		
	
	if (checkSat(pid)) {
		return getValues(pid, getBoolVars(currentModel), getIntVars(currentModel));
	} else {
		return ();
	}
}

private set[str] getBoolVars(Model m) = {n | str n <- m, isRelVar(m[n])};
private set[str] getIntVars(Model m) = {n | str n <- m, \int(int _) := m[n]};

private bool isRelVar(\true()) = true;
private bool isRelVar(\false()) = true;
private default bool isRelVar(Formula _) = false;