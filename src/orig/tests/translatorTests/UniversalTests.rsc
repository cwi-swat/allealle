module orig::tests::translatorTests::UniversalTests

extend orig::tests::translatorTests::BaseTester;

test bool testUniversal_onePigeonAndHole_pigeonIsAlwaysThere() {
	str testProblem = 
		" {p1, h1}
		' Pigeon:1		[{\<p1\>},{\<p1\>}]
		' Hole:1 		[{},{\<h1\>}]
		' nest:2 		[{},{\<p1,h1\>}]
		' forall n:nest | one n.Hole
		' forall p:Pigeon | one p.nest
		";

	TranslationResult result = translate(testProblem);
	
	return result.formula == 
		and({
			var("Hole_h1"),
			var("nest_p1_h1")
		});
}

test bool testUniversal_onePigeonAndHole_allIsOptional() {
	str testProblem = 
		" {p1, h1}
		' Pigeon:1		[{},{\<p1\>}]
		' Hole:1 		[{},{\<h1\>}]
		' nest:2 		[{},{\<p1,h1\>}]
		' forall n:nest | one n.Hole
		' forall p:Pigeon | one p.nest
		";

	TranslationResult result = translate(testProblem);
	
	return result.formula == 
		and({
			or({
				var("nest_p1_h1"),
				not(var("Pigeon_p1"))
			}),
			or({
				not(var("nest_p1_h1")),
				var("Hole_h1")
			})
		});
}

test bool testUniversal_morePigeonsAndHoles_neverEnoughHoles() {
	str testProblem = 
		" {p1, p2, p3, h1, h2}
		' Pigeon:1		[{\<p1\>,\<p2\>,\<p3\>},{\<p1\>,\<p2\>,\<p3\>}]
		' Hole:1 		[{},{\<h1\>,\<h2\>}]
		' nest:2 		[{},{\<p1,h1\>,\<p1,h2\>,\<p2,h1\>,\<p2,h2\>,\<p3,h1\>,\<p3,h2\>}]
		' forall p:Pigeon | one p.nest
		' forall n:nest | one n.Hole
		";

	TranslationResult result = translate(testProblem);
	
	iprintln(result.formula);
	
	return result.formula == \false();
}

