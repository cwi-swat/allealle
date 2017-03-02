module theories::relational::tests::translatorTests::EqualityTester

extend theories::relational::tests::translatorTests::BaseTester;

test bool testEquality_isEqual_noLowerBounds() {
	str testProblem = 
		" {a,b}
		' RelA:1 [{},{\<a\>,\<b\>}]
		' RelB:1 [{},{\<a\>,\<b\>}] 
		' RelA == RelB
		";

	Formula result = translate(testProblem);  

	return result == 
		and({
			and({
        or({
            var("RelA_b"),
            not(var("RelB_b"))
          }),
        or({
            var("RelA_a"),
            not(var("RelB_a"))
          })
      }),
    or({
        var("RelB_b"),
        not(var("RelA_b"))
      }),
    or({
        var("RelB_a"),
        not(var("RelA_a"))
      })
  });
}

test bool testEquality_isEqual_withLowerBounds() {
	str testProblem = 
		" {a,b}
		' RelA:1 [{\<a\>},{\<a\>,\<b\>}]
		' RelB:1 [{\<a\>},{\<a\>,\<b\>}] 
		' RelA == RelB
		";

	Formula result = translate(testProblem);  
	
	return result == 
		and({
			or({
				not(var("RelA_b")), 
				var("RelB_b")
			}),
			or({
				not(var("RelB_b")), 
				var("RelA_b")
			})
		});
}

test bool testEquality_neverEqual() {
	str testProblem = 
		" {a,b}
		' RelA:1 [{\<a\>},{\<a\>}]
		' RelB:1 [{\<b\>},{\<b\>}] 
		' RelA == RelB
		";

	Formula result = translate(testProblem);  
		
		
	return result == \false();
}

test bool testEquality_alwaysEqual() {
	str testProblem = 
		" {a,b}
		' RelA:1 [{\<a\>},{\<a\>}]
		' RelB:1 [{\<a\>},{\<a\>}] 
		' RelA == RelB
		";

	Formula result = translate(testProblem);  
	
	return result == \true();
}


