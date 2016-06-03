module extended::tests::translatorTests::GreaterThenTester

extend extended::tests::translatorTests::BaseTester;

test bool testGreaterThen_allVars() {
	str problem = "{a,b,c}
				  'Num(int):1[{},{\<a\>,\<b\>,\<c\>}]
				  'Num \> 10";
				  
	Formula result = translate(problem);	
	
	iprintln(result);
}

test bool testGreaterThen_allTruthValues() {
	str problem = "{a,b,c}
				  'Num(int):1[{\<a\>,\<b\>,\<c\>},{\<a\>,\<b\>,\<c\>}]
				  'Num \> 10";
				  
	Formula result = translate(problem);	
	
	iprintln(result);
}

test bool testGreaterThen_mixedVarsAndTruthValues() {
	str problem = "{a,b,c}
				  'Num(int):1[{\<a\>,\<b\>},{\<a\>,\<b\>,\<c\>}]
				  'Num \> 10";
				  
	Formula result = translate(problem);	
	
	iprintln(result);
}