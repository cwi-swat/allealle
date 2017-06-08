module theories::tests::translatorTests::DifferenceTester

extend theories::tests::translatorTests::BaseTester;

test bool testDifference() {
	str testProblem = 
		" {a,b}
		' Set:1 [{\<a\>,\<b\>},{\<a\>,\<b\>}]
		' no Set \\ Set
		";

	Formula result = translate(testProblem);
	
	return result == \true();
}