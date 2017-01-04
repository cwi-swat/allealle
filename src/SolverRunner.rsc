module SolverRunner

extend smt::solver::SolverRunner;

import SMTInterface; 
import AST;

import logic::Propositional;

import relational::AST;

Model getValues(SolverPID pid, set[SMTVar] vars, list[SMTInterpreter] interpreters) {
	resp = runSolver(pid, "(get-value (<intercalate(" ", [v.name | v <- vars])>))");
	
	if (resp != "") {
	  map[str,str] foundValues = (() | it + (var:val) | /(<var:[A-Za-z_0-9]*> <val:[^(^)]*>)/ := substring(resp, 1, size(resp)-1));
	
		return (() | it + interpreter.getValues(foundValues, vars) | SMTInterpreter interpreter <- interpreters); 
	}
	
	throw "Unable to get values for variables from solver";
}
 
Model firstModel(SolverPID pid, set[SMTVar] vars, list[SMTInterpreter] interpreters) = getValues(pid, vars, interpreters);

Model nextModel(SolverPID pid, Model currentModel, list[SMTInterpreter] interpreters) {
	if ("" !:= runSolver(pid, "(assert (or <intercalate(" ", [var | v <- currentModel, v.theory == relational(), str var := (currentModel[v] == \true() ? "(not <v.name>)" : v)])>))")) {
		throw "Unable to declare needed variables in SMT";
	}		
	
	if (checkSat(pid)) {
		return getValues(pid, domain(currentModel), interpreters);
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
