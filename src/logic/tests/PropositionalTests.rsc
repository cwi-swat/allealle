module logic::tests::PropositionalTests

import logic::Propositional;

test bool ifTrueThenAElseB() = \ite(\true(), var("a"), var("b")) == or({var("a"), not(var("b"))});
test bool ifFalseThenAElseB() = \ite(\false(), var("a"), var("b")) == or({not(var("a")), var("b")});

test bool orWithQAndNotQAndROnlyContainsR() = \or({var("q"), not(var("q")), var("r")}) == var("r");
