module orig::tests::translatorTests::SubsetTests

extend orig::tests::translatorTests::BaseTester; 

test bool testSubset_inSubset_lowerBoundSet() {
	str testProblem = 
		" {a,b}
		' RelA:1 [{\<a\>},{\<a\>,\<b\>}]
		' RelB:1 [{},{\<a\>,\<b\>}] 
		' RelA in RelB
		";

	TranslationResult result = translate(testProblem);  
	
	return result.formula == 
		and({
			var("RelB_a"),
			or({
				not(var("RelA_b")), 
				var("RelB_b")
			})
		});
}

test bool testSubset_inSubset_noLowerBoundSet() {
	str testProblem = 
		" {a,b}
		' RelA:1 [{},{\<a\>,\<b\>}]
		' RelB:1 [{},{\<a\>,\<b\>}] 
		' RelA in RelB
		";

	TranslationResult result = translate(testProblem);  
	
	return result.formula == 
		and({
			or({
				not(var("RelA_a")),
				var("RelB_a")
			}),
			or({
				not(var("RelA_b")), 
				var("RelB_b")
			})
		});
}

test bool testSubset_emptySetIsAProperSubset() {
	str testProblem = 
		" {a,b}
		' RelA:1 [{},{\<a\>}]
		' RelB:1 [{},{\<b\>}] 
		' RelA in RelB
		";

	TranslationResult result = translate(testProblem);  

	return result.formula == not(var("RelA_a")); 
}

test bool testSubset_neverASubset() {
	str testProblem = 
		" {a,b}
		' RelA:1 [{\<a\>},{\<a\>}]
		' RelB:1 [{},{\<b\>}] 
		' RelA in RelB
		";

	TranslationResult result = translate(testProblem);  
	
	return result.formula == \false(); 
}

test bool testSubset_alwaysASubset() {
	str testProblem = 
		" {a,b}
		' RelA:1 [{\<a\>},{\<a\>}]
		' RelB:1 [{\<a\>},{\<a\>,\<b\>}] 
		' RelA in RelB
		";

	TranslationResult result = translate(testProblem);  
	
	iprintln(result.formula);
	
	return result.formula == \true(); 
}
