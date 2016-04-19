module orig::tests::TranslatorTester

import orig::Imploder;
import orig::AST;
import orig::Translator;

import IO;

str testProblem() = 
	" {a,b,c}
	' Rel:1 [{\<a\>},{\<a\>,\<b\>,\<c\>}]
	' one Rel
	";

void testTranslation() = testTranslation(|project://allealle/examples/pigeonhole.alle|);
void testTranslation(loc file) {
	Problem p = implodeProblem(file);
	TranslationResult result = translate(p);  
	
	println(result.formula);
	println(result.env);
}

void testTranslationOfTestSyntax() {
	Problem p = implodeProblem(testProblem());
	TranslationResult result = translate(p);  
	
	println(result.formula);
	println(result.env);
}