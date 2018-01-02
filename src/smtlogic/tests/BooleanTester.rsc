module logic::tests::BooleanTester

import logic::Boolean;

test bool notTrueIsFalse() = \not(\true()) == \false();
test bool notFalseIsTrue() = \not(\false()) == \true();  
test bool notNotTrueIsTrue() = \not(\not(\true())) == \true();

test bool orWithOnlyTrueIsTrue() = \or({\true()}) == \true();
test bool orWithFalseAndTrueIsTrue() = \or(\false(),\true()) == \true();
test bool orWithFalseOrFalseIsFalse() = \or(\false(),\false()) == \false();
test bool orWithNestedOrIsFlattenedToTrue() = \or(\false(), \or({\true()})) == \true();
test bool orWithTrueAndNotTrueAndFalseIsTrue() = \or(\true(), or(not(\true()), \false())) == \true();

test bool andWithOnlyTrueIsTrue() = \and({\true()}) == \true();
test bool andWithFalseAndTrueIsFalse() = \and(\false(),\true()) == \false();
test bool andWithFalseAndFalseIsFalse() = \and(\false(),\false()) == \false();
test bool andWithNestedAndIsFlattened() = \and(\false(), \and({\true()})) == \false();
test bool andWithTrueAndNotTrueAndFalseIsFalse() = \and(\true(), \and(not(\true()), \false())) == \false();

test bool iteIfTrueThenFalseElseTrueIsFalse() = \ite(\true(), \false(), \true()) == \false();
test bool iteIfFalseThenTrueElseFalseIsFalse() = \ite(\false(), \true(), \false()) == \false();

test bool ifTrueThenFalseIsFalse() = \if(\true(),\false()) == \false();
test bool fiTrueThenFalseIfTrue() = \fi(\true(),\false()) == \true();
