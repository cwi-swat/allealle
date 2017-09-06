module theories::tests::binderTests::ProductTester

extend theories::tests::binderTests::TesterBase;

test bool test1x1Product_onlyThruthValues() {
	RelationMatrix dir = t(["d1"]);
	RelationMatrix file = t(["f1"])+t(["f2"]);
	
	RelationMatrix content = product(dir,file); 
	
	return content == t(["d1","f1"])+t(["d1","f2"]); 	
}
 
test bool test1x1Product_withVars() {
	RelationMatrix dir = v(["d1"]);
	RelationMatrix file = v(["f1"])+v(["f2"]);
	
	RelationMatrix content = product(dir,file);
	
	println(content);
	
	return content == val(["d1","f1"], \and({var("d1"),var("f1")}))+val(["d1","f2"], \and({var("d1"),var("f2")})); 	
}