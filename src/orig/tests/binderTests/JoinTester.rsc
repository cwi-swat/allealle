module orig::tests::binderTests::JoinTester

extend orig::tests::binderTests::BinderTesterBase;

test bool test1x2Join_onlyTruthValues() {
	Universe uni = universe(["jouke","sara","lucie"]);

	Binding person = t("jouke") + t("sara") + t("lucie");
	Binding parent = rest(t("jouke","lucie") + t("sara","lucie"), uni, \false());
		
	return 	\join(person, parent) == rest(t("lucie"), uni, \false());
}

test bool test2x1Join_onlyTruthValues() {
	Universe uni = universe(["jouke","sara","lucie"]);

	Binding person = t("jouke") + t("sara") + t("lucie");
	Binding parent = rest(t("jouke","lucie") + t("sara","lucie"), uni, \false());
		
	return 	\join(parent, person) == rest(t("jouke")+t("sara"), uni, \false());				 
}

test bool test1x2Join_withVars() {
	Universe uni = universe(["jouke","sara","lucie"]);

	Binding person = t("jouke")+t("sara")+t("lucie");
	Binding parent = rest(v("jouke","lucie")+v("sara","lucie"), uni, \false());
		
	return 	\join(person, parent) == rest(val("lucie", \or({var("jouke_lucie"), var("sara_lucie")})), uni, \false());
}

test bool test2x1Join_withVars() {
	Universe uni = universe(["jouke","sara","lucie"]);

	Binding person = t("jouke")+t("sara")+t("lucie");
	Binding parent = rest(v("jouke","lucie")+v("sara","lucie"), uni, \false());
		
	return \join(parent, person) == rest(val("jouke", var("jouke_lucie"))+val("sara", var("sara_lucie")), uni, \false());				 
}

test bool test2x2_onlyTruthValues() {
	Universe uni = universe(["jouke","heily","lucie"]);
	
	Binding person = t("jouke")+t("heily")+t("lucie");
	Binding parent = rest(t("jouke","lucie")+t("heily","jouke"), uni, \false());
	
	return \join(parent,parent) == rest(t("heily","lucie"), uni, \false());
}