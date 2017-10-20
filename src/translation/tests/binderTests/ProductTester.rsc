module translation::tests::binderTests::ProductTester

extend translation::tests::binderTests::TesterBase;

test bool test1x1Product_onlyThruthValues() {
	dir = truth(["d1"]);
	file = truths([["f1"],["f2"]]);
	
	uni = constructUniverse([dir,file]);
	
  SimpleRelationMatrix content = convert(product(convert(dir,uni),convert(file,uni)), uni); 
	
	println(content);
	
	return content == truths([["d1","f1"],["d1","f2"]]); 	
}
