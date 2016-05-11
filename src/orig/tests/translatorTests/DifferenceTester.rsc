module orig::tests::translatorTests::DifferenceTester

extend orig::tests::translatorTests::BaseTester;

test bool testDifference() {
	str testProblem = 
		" {a,b}
		' Set:1 [{\<a\>,\<b\>},{\<a\>,\<b\>}]
		' no Set - Set
		";

	TranslationResult result = translate(testProblem);
	
	return result.formula == \true();
}