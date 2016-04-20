module orig::tests::TranslatorTester

import orig::Imploder;
import orig::AST;
import orig::Translator;
import orig::smt::Translator;

import IO;

str testProblem() = 
	" {a,b,c,d}
	' Rel:1 [{\<a\>},{\<a\>,\<b\>,\<c\>}]
	' RelB:1 [{},{\<d\>,\<a\>,\<c\>}] 
	' Rel in RelB
	";

void testTranslation() = testTranslation(|project://allealle/examples/filesystem.alle|);
void testTranslation(loc file) {
	Problem p = implodeProblem(file);
	TranslationResult result = translate(p);  
	
	iprintln(result.formula);
	println(result.environment);
	
	compileAndSave(result.formula, result.environment, |project://allealle/output/out.smt2|);
}

void testTranslationOfTestSyntax() {
	Problem p = implodeProblem(testProblem());
	TranslationResult result = translate(p);  
	
	iprintln(result.formula);
	println(result.environment);
	
	compileAndSave(result.formula, result.environment, |project://allealle/output/out.smt2|);
}