module theories::integer::tests::BinderTester

extend theories::tests::binderTests::TesterBase;

import logic::Integer;

import theories::integer::AST;
import theories::integer::Binder;
import theories::relational::AST;

import IO;

private Binding c(list[Atom] vector, int i) = (<intTheory(),vector>:\int(i)) + t(vector); 
private Binding iValMan(list[Atom] vector)    = (<intTheory(),vector>:\intVar("<relVar(vector)>_int")) + t(vector);
private Binding iValOpt(list[Atom] vector)    = (<intTheory(),vector>:\intVar("<relVar(vector)>_int")) + v(vector);
private Binding iFormMan(list[Atom] vector, Formula f) = (<intTheory(),vector>:f) + t(vector);
private Binding iFormOpt(list[Atom] vector, Formula f) = (<intTheory(),vector>:f) + v(vector);

test bool multiplicationOfTwoUnaryMandatoryRelationsShouldProduceBinaryRelationWithTruthValues() {
  Binding intRel1 = iValMan(["a"]) + iValMan(["b"]);
  Binding intRel2 = iValMan(["c"]) + iValMan(["d"]);
    
  Binding result = multiply(intRel1, intRel2); 
  
  return result == (<relTheory(),["a","c"]>: \true(), <intTheory(), ["a","c"]>: multiplication(intVar("a_int"), intVar("c_int"))) +
                   (<relTheory(),["a","d"]>: \true(), <intTheory(), ["a","d"]>: multiplication(intVar("a_int"), intVar("d_int"))) +
                   (<relTheory(),["b","c"]>: \true(), <intTheory(), ["b","c"]>: multiplication(intVar("b_int"), intVar("c_int"))) + 
                   (<relTheory(),["b","d"]>: \true(), <intTheory(), ["b","d"]>: multiplication(intVar("b_int"), intVar("d_int")));  
}

test bool multiplicationOfTwoUnaryOptionalRelationsShouldProductBinaryRelationWithVariables() {
  Binding intRel1 = iValOpt(["a"]) + iValOpt(["b"]);
  Binding intRel2 = iValOpt(["c"]) + iValOpt(["d"]);
    
  Binding result = multiply(intRel1, intRel2); 
  
  return result == (<relTheory(),["a","c"]>: \and({var("a"), var("c")}), <intTheory(), ["a","c"]>: multiplication(intVar("a_int"), intVar("c_int"))) +
                   (<relTheory(),["a","d"]>: \and({var("a"), var("d")}), <intTheory(), ["a","d"]>: multiplication(intVar("a_int"), intVar("d_int"))) +
                   (<relTheory(),["b","c"]>: \and({var("b"), var("c")}), <intTheory(), ["b","c"]>: multiplication(intVar("b_int"), intVar("c_int"))) + 
                   (<relTheory(),["b","d"]>: \and({var("b"), var("d")}), <intTheory(), ["b","d"]>: multiplication(intVar("b_int"), intVar("d_int")));  
}


@doc {
  This test represent the operation Rel1*Rel2*Rel3. All relations are unary and contain maximal only one element. 
  Outcome should be a teneray relation representing the product of Rel1->Rel2->Rel3. 
}
test bool multiplicationsOnBinaryRelationWithOptionalUnaryRelationShouldProduceTenaryRelationWithVariables() {
  Binding intRel1 = iValOpt(["a"]) + iValOpt(["a"]);
  Binding intRel2 = iValOpt(["b"]) + iValOpt(["b"]);
  Binding intRel3 = iValOpt(["c"]) + iValOpt(["c"]);
    
  Binding result = multiply(multiply(intRel1, intRel2), intRel3); 
  
  return result == (<relTheory(),["a","b","c"]>: \and({var("a"), var("b"), var("c")}), <intTheory(), ["a","b","c"]>: multiplication(multiplication(intVar("a_int"), intVar("b_int")), intVar("c_int")));
}

@doc {
  This test represents the operation of Rel1/Rel2. All relations are unary.
  Outcome should be a binary relation representing the product of Rel1->Rel2
}
test bool divisionWithOptionalUnaryRelationsShouldProduceBinaryRelationWithVariables() {
  Binding intRel1 = iValOpt(["a"]) + iValOpt(["b"]);
  Binding intRel2 = iValOpt(["c"]) + iValOpt(["d"]);
    
  Binding result = divide(intRel1, intRel2); 
  
  return result == (<relTheory(),["a","c"]>: \and({var("a"), var("c")}), <intTheory(), ["a","c"]>: division(intVar("a_int"), intVar("c_int"))) +
                   (<relTheory(),["a","d"]>: \and({var("a"), var("d")}), <intTheory(), ["a","d"]>: division(intVar("a_int"), intVar("d_int"))) +
                   (<relTheory(),["b","c"]>: \and({var("b"), var("c")}), <intTheory(), ["b","c"]>: division(intVar("b_int"), intVar("c_int"))) + 
                   (<relTheory(),["b","d"]>: \and({var("b"), var("d")}), <intTheory(), ["b","d"]>: division(intVar("b_int"), intVar("d_int")));  
}
