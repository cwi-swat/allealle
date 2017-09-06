module theories::tests::translatorTests::UniversalTester

extend theories::tests::translatorTests::BaseTester;

test bool testUniversal_onePigeonAndHole_pigeonIsAlwaysThere() {
	str testProblem = 
		" {p1, h1}
		' Pigeon:1		[{\<p1\>},{\<p1\>}]
		' Hole:1 		[{},{\<h1\>}] 
		' nest:2 		[{},{\<p1,h1\>}]
		' forall n:nest | one n.Hole
		' forall p:Pigeon | one p.nest
		";

	Formula result = translate(testProblem);
	
	return result == 
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

	Formula result = translate(testProblem);
	
	return result == 
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
