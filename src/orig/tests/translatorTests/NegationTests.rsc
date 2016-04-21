module orig::tests::translatorTests::NegationTests

extend orig::tests::translatorTests::BaseTester;

test bool testNegation_noLowerBounds() {
	str testProblem = 
		" {a,b}
		' RelA:1 [{},{\<a\>,\<b\>}]
		' RelB:1 [{},{\<a\>,\<b\>}] 
		' not (RelA in RelB)
		";

	TranslationResult result = translate(testProblem);  
	
	return result.formula == 
		not(
			and({
				or({
					not(var("RelA_a")),
					var("RelB_a")
				}),
				or({
					not(var("RelA_b")), 
					var("RelB_b")
				})
			})
		);
}

test bool testNegation_withLowerBounds() {
	str testProblem = 
		" {a,b}
		' RelA:1 [{\<a\>},{\<a\>,\<b\>}]
		' RelB:1 [{},{\<a\>,\<b\>}] 
		' not (RelA in RelB)
		";

	TranslationResult result = translate(testProblem);  
	
	return result.formula == 
		not(
			and({
				var("RelB_a"),
				or({
					not(var("RelA_b")), 
					var("RelB_b")
				})
			})
		);
}
