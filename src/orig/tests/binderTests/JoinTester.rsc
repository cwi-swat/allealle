module orig::tests::binderTests::JoinTester

extend orig::tests::binderTests::BinderTesterBase;

test bool test1x2Join_onlyTruthValues() {
	Binding person = t("jouke") + t("sara") + t("lucie");
	Binding parent = t("jouke","lucie") + t("sara","lucie");

	return 	\join(person, parent) == t("lucie");
}

test bool test2x1Join_onlyTruthValues() {
	Binding person = t("jouke") + t("sara") + t("lucie");
	Binding parent = t("jouke","lucie") + t("sara","lucie");
		
	return 	\join(parent, person) == t("jouke")+t("sara");				 
}

test bool test1x2Join_withVars() {
	Binding person = t("jouke")+t("sara")+t("lucie");
	Binding parent = v("jouke","lucie")+v("sara","lucie");
		
	return 	\join(person, parent) == val("lucie", \or({var("jouke_lucie"), var("sara_lucie")}));
}

test bool test2x1Join_withVars() {
	Binding person = t("jouke")+t("sara")+t("lucie");
	Binding parent = v("jouke","lucie")+v("sara","lucie");
		
	return \join(parent, person) == val("jouke", var("jouke_lucie"))+val("sara", var("sara_lucie"));				 
}

test bool test2x2_onlyTruthValues() {
	Binding person = t("jouke")+t("heily")+t("lucie");
	Binding parent = t("jouke","lucie")+t("heily","jouke");
	
	return \join(parent,parent) == t("heily","lucie");
}

test bool test2x2_withVars() {
	Binding r = v("a","a")+v("a","b")+v("b","a")+v("b","b");
		
	return \join(r,r) == val("a", "a", \or({var("a_a"), \and({var("a_b"),var("b_a")})})) +
						 val("a", "b", \or({\and({var("a_a"), var("a_b")}), \and({var("a_b"), var("b_b")})})) +
						 val("b", "a", \or({\and({var("b_a"), var("a_a")}), \and({var("b_b"), var("b_a")})})) +
						 val("b", "b", \or({\and({var("b_a"), var("a_b")}), var("b_b")}));			
}

test bool test2x2_withVarsAndTruthVals() {
	Binding r = t("a","a")+v("a","b")+v("b","a");

	return \join(r,r) == t("a", "a") +
						 val("a", "b", var("a_b")) +
						 val("b", "a", var("b_a")) +
						 val("b", "b", \and({var("b_a"), var("a_b")}));
}

test bool test1x2_withVarsAndTruthVals() {
	Binding p = t("p");
	Binding n = v("p","h");
	
	return \join(p,n) == val("h", var("p_h"));
}