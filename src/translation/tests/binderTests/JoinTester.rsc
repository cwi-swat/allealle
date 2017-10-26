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

test bool test1x2Join_withVars() {
  RelationMatrix person = truths([["j"],["s"],["l"]]);
	RelationMatrix parent = vars([["j","l"],["s","l"]], "parent");
		
	return 	dotJoin(person, parent) == (["l"]: relOnly(\or({var("parent_j_l"), var("parent_s_l")})));
}
//
test bool test2x1Join_withVars() {
  RelationMatrix person = truths([["j"],["s"],["l"]]);
  RelationMatrix parent = vars([["j","l"],["s","l"]], "parent");
		
	return dotJoin(parent, person) == (["j"]:relOnly(var("parent_j_l")), ["s"]:relOnly(var("parent_s_l")));				 
}

test bool test2x2_onlyTruthValues() {
	RelationMatrix parent = truths([["j","l"],["h","j"]]);
	
	return dotJoin(parent,parent) == truth(["h","l"]);
}

test bool test2x2_withVars() {
	RelationMatrix r = vars([["a","a"],["a","b"],["b","a"],["b","b"]],"rel");
		
	return dotJoin(r,r) == (["a","a"]:relOnly(\or({var("rel_a_a"), \and({var("rel_a_b"), var("rel_b_a")})})),
						              ["a","b"]:relOnly(\or({\and({var("rel_a_a"), var("rel_a_b")}), \and({var("rel_a_b"), var("rel_b_b")})})),
						              ["b","a"]:relOnly(\or({\and({var("rel_b_a"), var("rel_a_a")}), \and({var("rel_b_b"), var("rel_b_a")})})),
						              ["b","b"]:relOnly(\or({\and({var("rel_b_a"), var("rel_a_b")}), var("rel_b_b")})));			
}

test bool test2x2_withVarsAndTruthVals() {
	RelationMatrix r = build([truth(["a","a"]),vars([["a","b"],["b","a"]],"rel")]);

	return dotJoin(r,r) == build([truth(["a","a"]),
	                              vars([["a","b"],["b","a"]],"rel"),
	                              (["b","b"]:relOnly(\and({var("rel_a_b"),var("rel_b_a")})))]);
}

test bool test1x2_withVarsAndTruthVals() {
	RelationMatrix p = truth(["p"]);
	RelationMatrix n = var(["p","h"],"rel");
	
	return dotJoin(p,n) == (["h"]:relOnly(var("rel_p_h")));
}

test bool test1x3_withTruthValues() {
  RelationMatrix nums = truth(["n1"]); 
  RelationMatrix cells = truths([["n1","n1","n9"],["n1", "n2", "n2"],["n1", "n3", "n3"]]);

  return dotJoin(nums, dotJoin(nums, cells)) == truth(["n9"]);  
}