module theories::relational::tests::translatorTests::DifferenceTester

extend theories::relational::tests::translatorTests::BaseTester;

test bool testDifference() {
	str testProblem = 
		" {a,b}
		' Set:1 [{\<a\>,\<b\>},{\<a\>,\<b\>}]
		' no Set \\ Set
		";

	Formula result = translate(testProblem);
	
	return result == \true();
}