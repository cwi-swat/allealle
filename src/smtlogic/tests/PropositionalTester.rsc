module smtlogic::tests::PropositionalTester

import smtlogic::Core;

test bool orWithQAndNotQAndROnlyContainsR() = \or(pvar("q"), not(pvar("q"))) == \true();
