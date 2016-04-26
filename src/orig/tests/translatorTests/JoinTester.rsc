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

test bool testJoin_MoreEggsInOneNest() {
	str testProblem = 
		" {n1, n2, e1, e2, e3}
		' Eggs:1		[{},{\<e1\>,\<e2\>,\<e3\>}]
		' nest:2		[{},{\<e1,n1\>,\<e1,n2\>,\<e2,n1\>,\<e2,n2\>,\<e3,n1\>,\<e3,n2\>}]
		' forall e:Eggs | one e.nest
		";

	TranslationResult result = translate(testProblem);
	
	iprintln(result.formula);
	
	return result.formula == 
		and({
			var("nest_p1_h1"),
			var("Pigeon_p1")
		});
}

