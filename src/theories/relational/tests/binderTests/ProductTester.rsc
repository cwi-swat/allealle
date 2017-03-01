module theories::relational::tests::binderTests::ProductTester

extend theories::relational::tests::binderTests::TesterBase;

test bool test1x1Product_onlyThruthValues() {
	Binding dir = t("d1");
	Binding file = t("f1")+t("f2");
	
	Binding content = product(dir,file); 
	
	return content == t("d1","f1")+t("d1","f2");	
}
 
test bool test1x1Product_withVars() {
	Binding dir = v("d1");
	Binding file = v("f1")+v("f2");
	
	Binding content = product(dir,file);
	
	return content == val("d1","f1", \and({var("d1"),var("f1")}))+val("d1","f2", \and({var("d1"),var("f2")}));	
}