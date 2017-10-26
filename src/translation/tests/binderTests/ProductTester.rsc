module translation::tests::binderTests::ProductTester

extend translation::tests::binderTests::TesterBase;

test bool test1x1Product_onlyThruthValues() {
	RelationMatrix dir = truth(["d1"]);
	RelationMatrix file = truths([["f1"],["f2"]]);
	
	RelationMatrix content = product(dir,file); 
	
	return content == truths([["d1","f1"],["d1","f2"]]); 	
}
 
test bool test1x1Product_withVars() {
	RelationMatrix dir = var(["d1"],"dir");
	RelationMatrix file = vars([["f1"],["f2"]],"file");
	
	RelationMatrix content = product(dir,file);
	
	return content == (["d1","f1"]:relOnly(\and({var("dir_d1"),var("file_f1")})),["d1","f2"]:relOnly(\and({var("dir_d1"),var("file_f2")}))); 	
}