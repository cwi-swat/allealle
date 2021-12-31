module benchmark::relational::handshake::AlleAlleHandshakeBenchmark

extend benchmark::AlleAlleBenchmark;

import List;

void runHandshakeBenchmark(str postfix = "") 
  = runBenchmark([10..17], "relational", "handshake", true, postfix = postfix); 

str constructRels(int config) {
  str rels = "Person (pId:id) = {<intercalate(",", ["\<p<i>\>" | i <- [1..config+1]])>}
    'Jocelyn (pId:id) = {\<p1\>}
    'Hilary (pId:id) = {\<p2\>}
    'spouse (pId:id, sp:id) \>= {\<p1,p2\>,\<p2,p1\>} \<= {<intercalate(",", ["\<p<i>,p<j>\>" | i <- [3..config+1], j <- [3..config+1]])>}
    'shaken (pId:id, other:id) \<= {<intercalate(",", ["\<p<i>,p<j>\>" | i <- [1..config+1], j <- [1..config+1]])>}
    'nrOfShakes (pId:id, nr:int) = {<intercalate(",", ["\<p<i>,?\>" | i <- [1..config+1]])>}";
    
    return rels;
}

str getConstraints(int config)
  = "spouse ⊆ Person ⨯ Person[pId as sp]
    'shaken ⊆ Person ⨯ Person[pId as other]
    '
    '// Everybody can only have one spouse
    '∀ p ∈ Person | one (p ⨝ spouse)
    '// Spouse is a bijection
    'spouse = spouse[pId as sp, sp as pId]
    '// Nobody is its own spouse
    '∀ s ∈ spouse | s[pId] ≠ s[sp][sp as pId]
    '
    '// Nobody shakes it own hand
    '∀ s ∈ shaken | s[pId] ≠ s[other][other as pId]
    '// Nobody shakes the hand of spouse
    '∀ s ∈ shaken | no (s ⨝ spouse) where other = sp
    '
    '// If p shakes q\'s hand, q shakes p\'s hand, shaken is a bijection
    'shaken = shaken[pId as other, other as pId]
    '
    '∀ p ∈ Person | some (((p ⨝ shaken)[count() as shakes] ⨯ p) ⨝ nrOfShakes) where nr = shakes";