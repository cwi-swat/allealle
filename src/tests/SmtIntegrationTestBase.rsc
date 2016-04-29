module tests::SmtIntegrationTestBase

import orig::AST;
import orig::Imploder;
import orig::Translator;
import orig::SMTCompiler;
import smt::solver::Z3;

import util::Benchmark;
import util::ShellExec;
import IO;
import List;

void executeTest(str title, str problem) {
	 println(title);
	 
	 print("Parsing and imploding problem...");
	 Problem p = implodeProblem(problem);
	 print("done\n");
	 
	 print("Translating problem to SAT formula...");
	 tuple[TranslationResult result, int time] t = benchmark(translate, p);
	 print("done\n");
	 
	 print("Compiling SAT formula to SMT...");
	 tuple[str smt, int time] s = benchmark(compileToSMT, t.result.formula);
	 print("done\n");
	 
	 print("Solving by Z3...");
	 tuple[str outcome, int time] solving = runInSolver(s.smt);
	 print("done\n");
	 
	 println("Done.");
	 println("Outcome is \'<solving.outcome>\'");
	 println("Translation to SAT formula took: <(t.time/1000000)> ms");
	 println("Compilation to SMT formula took: <(s.time/1000000)> ms");
	 println("Solving time in Z3: <solving.time/1000000> ms");
	 
	 //println("Formula:");
	 //iprintln(t.result.formula);
}

tuple[str, int] runInSolver(str smtProblem, set[str] varNames) {
	PID z3Pid = startZ3(); 
	try {
		tuple[str answer, int time] result = benchmark(\run, z3Pid, smtProblem + "\n(check-sat)");
		if (result.answer == "sat") {
			str modelValues = \run(z3Pid, "(get-value)");
		}
	} 
	catch ex: println(ex);
	finally {
		stopZ3(z3Pid);
	};
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
