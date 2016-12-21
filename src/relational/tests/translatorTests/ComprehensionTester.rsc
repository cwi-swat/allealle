module relational::tests::translatorTests::ComprehensionTester

extend relational::tests::translatorTests::BaseTester;

test bool testSmallComprehension() {
	str testProblem = 
		" {p1,p2}
		' Person:1 [{\<p1\>,\<p2\>},{\<p1\>,\<p2\>}]
		' parent:2 [{}, {\<p1,p2\>,\<p2,p1\>}]
		' child:2 [{}, {\<p1,p2\>,\<p2,p1\>}]
		' child in Person -\> Person
		' parent in Person -\> Person
		' child = {p:Person, pp:Person | pp in p.parent} 
		";

	Formula result = translate(testProblem);  
	iprintln(result);
}