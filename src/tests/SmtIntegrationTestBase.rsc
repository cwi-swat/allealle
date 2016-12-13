module tests::SmtIntegrationTestBase

import orig::AST;
import orig::Imploder;
import orig::FormulaTranslator;
import orig::SMTCompiler;
import logic::CNFConverter;
import orig::SolverRunner;

import util::Benchmark;
import util::ShellExec;
import IO;
import List;

void executeTest(loc file) = executeTest("File: <file>", readFile(file)); 

void executeTest(str title, str problem) {
	println(title);
	 
	print("Parsing and imploding problem...");
	Problem p = implodeProblem(problem);
	print("done\n");
	 
	print("Building initial relational environment...");
	tuple[Environment env, int time] ie = benchmark(createInitialEnvironment, p);
	print("done\n");	 
	 
	print("Translating problem to SAT formula...");
	tuple[Formula f, int time] trans = benchmark(translate, p, ie.env);
	print("done\n");
	 
	//print("Converting to CNF...");
	//tuple[Formula formula, int time] cnf = benchmark(convertToCNF, trans.f);
	//print("done\n");
	
	//print("Solving by Z3...");
	//
	//PID solverPid = startSolver();
	//try {
	//	set[str] vars = {name | /var(str name) := cnf.formula};
	//	tuple[CheckSatResult result, int time] solving = benchmark(isSatisfiable, solverPid, vars, cnf.formula); 
	//	print("done\n");
	//		 
	//	println("Done.");
	//	println("Outcome is \'<solving.result.sat>\'");
	//	println("Translation to SAT formula took: <(t.time/1000000)> ms");
	//	println("Converting to Conjunctive Normal Form took: <(cnf.time/1000000)> ms");
	//	println("Solving time in Z3: <solving.time/1000000> ms");
	//	
	//	if (solving.result.sat) {
	//		model = firstModel(solverPid, vars);
	//		println("First found model was:");
	//		iprintln(model);
	//	} else {
	//		println("Unsatisfiable; formulas in unsat core:");
	//		iprintln(getUnsatCore(solverPid, solving.result.labels));
	//	}
	//}
	//catch ex: println("Error while running solver, reason \'<ex>\'");
	//finally {
	//	stopSolver(solverPid);
	//}	
	
	println("Done.");
	println("Translation to SAT formula took: <(trans.time/1000000)> ms");	
	
	 
	//println("SAT Formula:");
	//iprintln(t.result.formula);
	// 
	//println("CNF Formula:");
	//iprintln(cnf.formula);	 
}

tuple[&T, int] benchmark(&T () methodToBenchmark) {
	int startTime = userTime();
	&T result = methodToBenchmark();
	return <result, userTime() - startTime>;
}

tuple[&T, int] benchmark(&T (&R) methodToBenchmark, &R p) {
	int startTime = userTime();
	&T result = methodToBenchmark(p);
	return <result, userTime() - startTime>;
}

tuple[&T, int] benchmark(&T (&R,&Q) methodToBenchmark, &R p1, &Q p2) {
	int startTime = userTime();
	&T result = methodToBenchmark(p1,p2);
	return <result, userTime() - startTime>;
}

tuple[&T, int] benchmark(&T (&R,&Q,&S) methodToBenchmark, &R p1, &Q p2, &S p3) {
	int startTime = userTime();
	&T result = methodToBenchmark(p1,p2,p3);
	return <result, userTime() - startTime>;
}
