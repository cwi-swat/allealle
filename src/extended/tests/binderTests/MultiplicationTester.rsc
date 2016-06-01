module extended::tests::binderTests::MultiplicationTester

extend extended::tests::binderTests::BinderTesterBase;
 

test bool testMultiplication_allLiterals() {
	Binding onlyLits = iV("a",1) + iV("b",1) + iV("c",1);
	
	return multiply(onlyLits, onlyLits) == val("a", \int(1))+val("b", \int(1))+val("c", \int(1)); 	
}

test bool testMultiplication_literalsAndVars() {
	Binding onlyLit = iV("a","2") + iV("b",2) + iV("c",2);
	Binding onlyVars = v("a")+v("b")
}
