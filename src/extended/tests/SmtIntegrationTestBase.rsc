module extended::tests::SmtIntegrationTestBase

import orig::AST;
import orig::Imploder;
import orig::Translator;
import logic::CNFConverter;
import orig::SolverRunner;

import extended::SMTCompiler;
import extended::ModelFinder;

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

	ModelFinderResult result = checkInitialSolution(p);
	 
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
