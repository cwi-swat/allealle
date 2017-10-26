module translation::tests::binderTests::JoinTester

extend translation::tests::binderTests::TesterBase;

test bool test1x2Join_onlyTruthValues() {
	RelationMatrix person = truths([["j"],["s"],["l"]]);
	RelationMatrix parent = truths([["j","l"],["s","l"]]); 
 
	return 	dotJoin(person, parent) == truth(["l"]);
}

test bool test2x1Join_onlyTruthValues() {
  RelationMatrix person = truths([["j"],["s"],["l"]]);
  RelationMatrix parent = truths([["j","l"],["s","l"]]); 
		
	return 	dotJoin(parent, person) == truths([["j"],["s"]]);				 
}

//test bool test1x2Join_withVars() {
//  RelationMatrix person = truths([["j"],["s"],["l"]]);
//	RelationMatrix parent = vars([["j","l"],["s","l"]], "parent");
//		
//	return 	dotJoin(person, parent) == val(["l"], \or({var("j_l"), var("s_l")}));
//}
//
//test bool test2x1Join_withVars() {
//	RelationMatrix person = t(["j"])+t(["s"])+t(["l"]);
//	RelationMatrix parent = v(["j","l"])+v(["s","l"]);
//		
//	return \join(parent, person, voidAdder) == val(["j"], var("j_l"))+val(["s"], var("s_l"));				 
//}
//
//test bool test2x2_onlyTruthValues() {
//	RelationMatrix person = t(["j"])+t(["heily"])+t(["l"]);
//	RelationMatrix parent = t(["j","l"])+t(["heily","j"]);
//	
//	return \join(parent,parent, voidAdder) == t(["heily","l"]);
//}
//
//test bool test2x2_withVars() {
//	RelationMatrix r = v(["a","a"])+v(["a","b"])+v(["b","a"])+v(["b","b"]);
//		
//	return \join(r,r, voidAdder) == val(["a", "a"], \or({var("a_a"), \and({var("a_b"),var("b_a")})})) +
//						 val(["a", "b"], \or({\and({var("a_a"), var("a_b")}), \and({var("a_b"), var("b_b")})})) +
//						 val(["b", "a"], \or({\and({var("b_a"), var("a_a")}), \and({var("b_b"), var("b_a")})})) +
//						 val(["b", "b"], \or({\and({var("b_a"), var("a_b")}), var("b_b")}));			
//}
//
//test bool test2x2_withVarsAndTruthVals() {
//	RelationMatrix r = t(["a","a"])+v(["a","b"])+v(["b","a"]);
//
//	return \join(r,r, voidAdder) == t(["a", "a"]) +
//						 val(["a", "b"], var("a_b")) +
//						 val(["b", "a"], var("b_a")) +
//						 val(["b", "b"], \and({var("b_a"), var("a_b")}));
//}
//
//test bool test1x2_withVarsAndTruthVals() {
//	RelationMatrix p = t(["p"]);
//	RelationMatrix n = v(["p","h"]);
//	
//	return \join(p,n, voidAdder) == val(["h"], var("p_h"));
//}
//
//test bool test1x3_withTruthValues() {
//  RelationMatrix nums = t(["n1"]); 
//  RelationMatrix cells = t(["n1", "n1", "n9"]) + t(["n1", "n2", "n2"]) + t(["n1", "n3", "n3"]);
//
//  return \join(nums, \join(nums, cells, voidAdder), voidAdder) == t(["n9"]);  
//}