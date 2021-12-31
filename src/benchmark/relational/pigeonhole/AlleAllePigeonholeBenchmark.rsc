module benchmark::relational::pigeonhole::AlleAllePigeonholeBenchmark
extend benchmark::AlleAlleBenchmark;

import List;

void runPigeonholeBenchmark(str postfix = "")  
  = runBenchmark([5..11], "relational", "pigeonhole", true, postfix = postfix); 

str constructRels(int config)
  = "Pigeon (pId: id)           =  {<intercalate(",", ["\<p<i>\>" | int i <- [0..config]])>}
    'Hole   (hId: id)           =  {<intercalate(",", ["\<h<i>\>" | int i <- [0..config-1]])>}
    'nest   (pId: id, hId: id) \<= {<intercalate(",", ["\<p<i>,h<j>\>" | int i <- [0..config], int j <- [0..config-1]])>}";
    
str getConstraints(int config) 
  = "nest ⊆ Pigeon ⨯ Hole
	'∀ p ∈ Pigeon | one   p ⨝ nest
	'∀ h ∈ Hole | lone  h ⨝ nest";
