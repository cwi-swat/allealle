module orig::tests::translatorTests::JoinTester

extend orig::tests::translatorTests::BaseTester;

test bool testJoin_AlwaysOnePigeon_MustBeOneNest() {
	str testProblem = 
		" {p1, h1}
		' Pigeon:1		[{\<p1\>},{\<p1\>}]
		' nest:2 		[{},{\<p1,h1\>}]
		' one Pigeon.nest
		";

	Formula result = translate(testProblem);
	
	return result == var("nest_p1_h1");
}

test bool testJoin_MustBeOnePigeon() {
	str testProblem = 
		" {p1, h1}
		' Pigeon:1		[{},{\<p1\>}]
		' nest:2 		[{},{\<p1,h1\>}]
		' one Pigeon.nest
		";

	Formula result = translate(testProblem);
	
	return result == 
		and({
			var("nest_p1_h1"),
			var("Pigeon_p1")
		});
}
