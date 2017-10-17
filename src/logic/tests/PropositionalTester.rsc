module logic::tests::PropositionalTester

import logic::Propositional;

test bool orWithQAndNotQAndROnlyContainsR() = \or(var("q"), not(var("q"))) == \true();

test bool orWithNestedAndsWithOverlappingElementsResultsInOr() =
  \or({\or({var("a"),var("b"),var("c")}), \and({var("d"),var("e"),var("b")})}) == \or({var("a"),var("b"),var("c")});

test bool andsWithNestedOrsWithOverlappingElementsResultsInAnd() =
  \and({\or({var("a"),var("b"),var("c")}), \and({var("d"),var("e"),var("b")})}) == \and({var("d"),var("e"),var("b")});
