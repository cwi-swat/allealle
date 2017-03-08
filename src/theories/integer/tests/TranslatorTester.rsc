module theories::integer::tests::TranslatorTester

extend theories::relational::tests::translatorTests::BaseTester;

import theories::integer::Translator;
import logic::Integer;
@doc {
  This test checks the constraint 'Rel1 > Rel2' meaning that all the present elements in Rel1 should be greather then the present elements in Rel2. 
}
test bool rel1SIsGreaterThenRel2() {
  str testProblem = 
  " {a,b,c,d}
  ' Rel1(int):1 [{},{\<a\>,\<b\>}]
  ' Rel2(int):1 [{},{\<c\>,\<d\>}] 
  ' Rel1 \> Rel2
  ";

  Formula result = translate(testProblem);
  
  return result == 
    \and({
      \or({\not(\and({var("Rel1_a"), var("Rel2_c")})), \gt(intVar("a"), intVar("c"))}),
      \or({\not(\and({var("Rel1_a"), var("Rel2_d")})), \gt(intVar("a"), intVar("d"))}),
      \or({\not(\and({var("Rel1_b"), var("Rel2_c")})), \gt(intVar("b"), intVar("c"))}),
      \or({\not(\and({var("Rel1_b"), var("Rel2_d")})), \gt(intVar("b"), intVar("d"))})
   });       
}


@doc {
  Test the theorom of Pythagoras on 3 relations meaning that RelC * RelC == RelA * RelA + RelB * RelB
}
test bool pythagorasOnRelations() {
  str testProblem = 
  " {a,b,c}
  ' RelA(int):1 [{},{\<a\>}]
  ' RelB(int):1 [{},{\<b\>}]
  ' RelC(int):1 [{},{\<c\>}] 
  ' RelC * RelC = RelA * RelA + RelB * RelB
  ";

  Formula result = translate(testProblem);
  
  return result == 
    \and({
      \or({\not(\and({var("RelA_a"), var("RelB_b"), var("RelC_c")})), 
        \equal(\multiplication(intVar("c"),intVar("c")), \addition(\multiplication(intVar("a"), intVar("a")), \multiplication(intVar("b"), intVar("b"))))})
    });       
}