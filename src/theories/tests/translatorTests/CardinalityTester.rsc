module theories::relational::tests::translatorTests::CardinalityTester

extend theories::relational::tests::translatorTests::BaseTester;

test bool testCardinality_some_noLowerBounds() {
	str testProblem = 
		" {a,b}
		' Rel:1 [{},{\<a\>,\<b\>}] 
		' some Rel
		";
 
	Formula result = translate(testProblem);  
	
	return result == 
		or({
			var("Rel_a"),
			var("Rel_b") 
		});
}

test bool testCardinality_some_withLowerBounds() {
	str testProblem = 
		" {a,b}
		' Rel:1 [{\<a\>},{\<a\>,\<b\>}]
		' some Rel
		";

	Formula result = translate(testProblem);  
	
	return result == \true();
}

test bool testCardinality_one_noLowerBounds() {
	str testProblem = 
		" {a,b}
		' Rel:1 [{},{\<a\>,\<b\>}]
		' one Rel
		";

	Formula result = translate(testProblem);  
	
	return result == 
		or({
			and({
				var("Rel_a"),
				not(var("Rel_b"))
			}),
			and({
				var("Rel_b"),
				not(var("Rel_a"))
			})
		});
}

test bool testCardinality_one_withLowerBounds() {
	str testProblem = 
		" {a,b}
		' Rel:1 [{\<a\>},{\<a\>,\<b\>}]
		' one Rel
		";

	Formula result = translate(testProblem);  

	return result == \not(var("Rel_b"));
}

test bool testCardinality_lone_moreAtoms_noLowerBounds() {
	str testProblem = 
		" {a,b,c}
		' Rel:1 [{},{\<a\>,\<b\>,\<c\>}]
		' lone Rel
		";

	Formula result = translate(testProblem); 
	
	return result == 
	  or({
			and({var("Rel_a"),
				not(var("Rel_b")),
				not(var("Rel_c"))
			}),
			and({var("Rel_b"),
				not(var("Rel_a")),
				not(var("Rel_c"))
			}),
			and({var("Rel_c"),
				not(var("Rel_b")),
				not(var("Rel_a"))
			}),
  		not(or({
  			var("Rel_a"),
  			var("Rel_b"),
  			var("Rel_c")
  		}))
  	});
}


test bool testCardinality_no_noLowerBounds() {
	str testProblem = 
		" {a,b}
		' Rel:1 [{},{\<a\>,\<b\>}]
		' no Rel
		";

	Formula result = translate(testProblem);  

	return result == 
		not(
			or({
				var("Rel_a"),
				var("Rel_b")
			})
		);
}

test bool testCardinality_no_withLowerBounds() {
	str testProblem = 
		" {a,b}
		' Rel:1 [{\<a\>},{\<a\>,\<b\>}]
		' no Rel
		";

	Formula result = translate(testProblem);  

	return result == \false();
}

test bool testCardinality_lone_noLowerBounds() {
	str testProblem = 
		" {a,b}
		' Rel:1 [{},{\<a\>,\<b\>}]
		' lone Rel
		";

	Formula result = translate(testProblem);  
	
	return result == 
		or({
			not(
				or({
					var("Rel_a"),
					var("Rel_b")
				})
			),
			and({
				var("Rel_a"),
				not(var("Rel_b"))
			}),
			and({
				var("Rel_b"),
				not(var("Rel_a"))
			})
		});
}

test bool testCardinality_lone_withLowerBounds() {
	str testProblem = 
		" {a,b}
		' Rel:1 [{\<a\>},{\<a\>,\<b\>}]
		' lone Rel
		";

	Formula result = translate(testProblem);  

	return result == not(var("Rel_b"));
}

test bool testCardinality_lone_binaryRelationOnlyOnePossibleRelation() {
	str testProblem =
		" {a,b}
		' rel:2 [{},{\<a,b\>}]
		' lone rel
		";
		
	Formula result = translate(testProblem);  
	
	return result == \true(); //var("rel_a_b");
}

test bool testCardinality_lone_binaryRelationTwoPossibleRelation() {
	str testProblem =
		" {a,b}
		' rel:2 [{},{\<a,a\>,\<a,b\>}]
		' lone rel
		";
		
	Formula result = translate(testProblem);  
	
	return result == 
		or({
			not(or({
				var("rel_a_a"),
				var("rel_a_b")
			})),
			and({
				var("rel_a_a"),
				not(var("rel_a_b"))
			}),
			and({
				not(var("rel_a_a")),
				var("rel_a_b")
			})
		});
	
}

