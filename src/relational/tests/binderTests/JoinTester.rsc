module relational::tests::binderTests::JoinTester

extend relational::tests::binderTests::TesterBase;

test bool test1x2Join_onlyTruthValues() {
	Binding person = t("j") + t("s") + t("l");
	Binding parent = t("j","l") + t("s","l");

	return 	\join(person, parent) == t("l");
}

test bool test2x1Join_onlyTruthValues() {
	Binding person = t("j") + t("s") + t("l");
	Binding parent = t("j","l") + t("s","l");
		
	return 	\join(parent, person) == t("j")+t("s");				 
}

test bool test1x2Join_withVars() {
	Binding person = t("j")+t("s")+t("l");
	Binding parent = v("j","l")+v("s","l");
		
	return 	\join(person, parent) == val("l", \or({var("j_l"), var("s_l")}));
}

test bool test2x1Join_withVars() {
	Binding person = t("j")+t("s")+t("l");
	Binding parent = v("j","l")+v("s","l");
		
	return \join(parent, person) == val("j", var("j_l"))+val("s", var("s_l"));				 
}

test bool test2x2_onlyTruthValues() {
	Binding person = t("j")+t("heily")+t("l");
	Binding parent = t("j","l")+t("heily","j");
	
	return \join(parent,parent) == t("heily","l");
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

test bool test1x3_withTruthValues() {
  Binding nums = t("n1"); 
  Binding cells = t("n1", "n1", "n9") + t("n1", "n2", "n2") + t("n1", "n3", "n3");

  return \join(nums, \join(nums, cells)) == t("n9");  
}