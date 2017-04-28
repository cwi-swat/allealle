module logic::tests::PropositionalTester

import logic::Propositional;

test bool orWithQAndNotQAndROnlyContainsR() = \or(var("q"), not(var("q"))) == \true();
