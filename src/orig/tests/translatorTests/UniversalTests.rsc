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

test bool testUniversalAndExistential_onePigeonAndHole_IfThereIsAPigeonThereIsAHole() {
	str testProblem = 
		" {p1, h1}
		' Pigeon:1		[{\<p1\>},{\<p1\>}]
		' Hole:1 		[{},{\<h1\>}]
		' nest:2 		[{},{\<p1,h1\>}]
		' forall p:Pigeon | one p.nest  
		' forall h:Hole | lone nest.h
		";

	TranslationResult result = translate(testProblem);
	
	iprintln(result.formula);
	
	return result.formula == 
		or({
			not(var("Pigeon_p1")),
			and({
				var("Hole_h1"),
				var("nest_p1_h1")
			})
		});
}
