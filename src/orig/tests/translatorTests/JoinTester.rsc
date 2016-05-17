module orig::tests::translatorTests::JoinTester

extend orig::tests::translatorTests::BaseTester;

test bool testJoin_AlwaysOnePigeon_MustBeOneNest() {
	str testProblem = 
		" {p1, h1}
		' Pigeon:1		[{\<p1\>},{\<p1\>}]
		' nest:2 		[{},{\<p1,h1\>}]
		' one Pigeon.nest
		";

	TranslationResult result = translate(testProblem);
	
	return result.formula == var("nest_p1_h1");
}

test bool testJoin_MustBeOneNest() {
	str testProblem = 
		" {p1, h1}
		' Pigeon:1		[{},{\<p1\>}]
		' nest:2 		[{},{\<p1,h1\>}]
		' one Pigeon.nest
		";

	TranslationResult result = translate(testProblem);
	
	return result.formula == 
		and({
			var("nest_p1_h1"),
			var("Pigeon_p1")
		});
}
