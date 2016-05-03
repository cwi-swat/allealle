module logic::tests::CNFConverterTester

import logic::CNFConverter;
import logic::Propositional;

test bool testNNF_notAandBIsNotAOrNotB() = convertToCNF(\not(\and({var("a"),var("b")}))) == \or({not(var("a")), not(var("b"))}); 
test bool testNNF_notAorBIsNotAAndNotB() = convertToCNF(\not(\or({var("a"),var("b")}))) == \and({not(var("a")), not(var("b"))});
test bool testNNF_notAandBandCIsNotAorNotBorNotC() = convertToCNF(\not(\and({var("a"), var("b"), var("c")}))) == \or({\not(var("a")), \not(var("b")), \not(var("c"))});

test bool testCNF_AorBandCIsAorBandAorC() = convertToCNF(\or({\var("a"), \and({var("b"), var("c")})})) == \and({\or({var("a"), var("b")}), \or({var("a"), var("c")})});
test bool testCNF_AandBorCisAorCandBorC() = convertToCNF(\or({\and({var("a"), var("b")}), var("c")})) == \and({\or({var("a"), var("c")}), \or({var("b"), var("c")})});

test bool testCNF_AandBandC_or_D_or_E_is_AorDorE_and_BorDorE_and_CorDorE() = convertToCNF(\or({\and({var("a"),var("b"),var("c")}), var("d"), var("e")})) == \and({\or({var("a"),var("d"),var("e")}),\or({var("b"),var("d"),var("e")}),\or({var("c"),var("d"),var("e")})});
 