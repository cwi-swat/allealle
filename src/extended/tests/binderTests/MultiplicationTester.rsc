module extended::tests::binderTests::MultiplicationTester

extend extended::tests::binderTests::BinderTesterBase;
 

test bool testMultiplication_allLiterals() {
	Binding onlyLits = iV("a",1) + iV("b",1) + iV("c",1);
	
	return multiply(onlyLits, onlyLits) == iV("a", \int(1))+iV("b", \int(1))+val("c", \int(1)); 	
}

test bool testMultiplication_literalsAndVars() {
	Binding onlyLit = iV("a",2) + iV("b",2) + iV("c",2);
	Binding onlyVars = iV("a")+iV("b")+iV("c");
	
	return multiply(onlyVars, onlyLit) ==
		iVal("a",multiplication({\int(2), var("a")}))+
		iVal("b",multiplication({\int(2), var("b")}))+
		iVal("c",multiplication({\int(2), var("c")}));		
}
