module benchmark::relational::rivercrossing::AlleAlleRiverCrossingBenchmark

extend benchmark::AlleAlleBenchmark;

void runRiverCrossingBenchmark(str postfix = "") 
  = runBenchmark([1], "relational", "rivercrossing", true, postfix = postfix);

str constructRels(int config) 
  = "State (sId:id)                \>= {\<s1\>} \<= {\<s1\>..\<s8\>}
    'InitialState (sId:id)          = {\<s1\>}
    'ordering (cur:id,next:id)     \<= {\<s1,s2\>,\<s2,s3\>,\<s3,s4\>,\<s4,s5\>,\<s5,s6\>,\<s6,s7\>,\<s7,s8\>}
    '
    'Passenger (pId:id)             = {\<goat\>,\<wolf\>,\<cabbage\>,\<farmer\>}
    'Farmer (pId:id)                = {\<farmer\>}
    '
    'eats (pId:id,eat:id)           = {\<goat,cabbage\>,\<wolf,goat\>}           
    '
    'near (sId:id,pId:id)          \>= {\<s1,goat\>,\<s1,cabbage\>,\<s1,farmer\>,\<s1,wolf\>} 
    '                              \<= {\<s1,goat\>..\<s8,goat\>,\<s1,cabbage\>..\<s8,cabbage\>,\<s1,farmer\>..\<s8,farmer\>,\<s1,wolf\>..\<s8,wolf\>} 
    ' 
    'far (sId:id,pId:id)           \<= {\<s1,goat\>..\<s8,goat\>,\<s1,cabbage\>..\<s8,cabbage\>,\<s1,farmer\>..\<s8,farmer\>,\<s1,wolf\>..\<s8,wolf\>}";
 
str getConstraints(int config) 
  = "ordering ⊆ State[sId as cur] ⨯ State[sId as next]
    'near ⊆ State ⨯ Passenger
    'far ⊆ State ⨯ Passenger
    '
    'State ⊆ (InitialState[sId as cur] ⨝ *ordering)[next][next as sId]
    '
    '// a Passenger can only be on one shore in each state
    '∀ s ∈ State | no (s ⨝ near ∩ s ⨝ far)
    '
    '// All states should have all passengers on one side or the other 
    '∀ s ∈ State | (s ⨝ near ∪ s ⨝ far)[pId] = Passenger
    '
    '// The goal is to get all Passengers to the other side compared to the start state
    '∃ s ∈ State | Passenger = (s ⨝ far)[pId] 
    '
    '// The farmer is always in the boat going from one shore to the other
    '//forall s1:State, s2: State | s1-\>s2 in ordering =\> (Farmer in s1.near =\> Farmer in s2.far) || (Farmer in s1.far =\> Farmer in s2.near)
    '∀ o ∈ ordering | let s1 = o[cur][cur as sId], s2 = o[next][next as sId] | 
    '  (Farmer ⊆ (s1 ⨝ near)[pId] ⇒ Farmer ⊆ (s2 ⨝ far)[pId]) ∨ (Farmer ⊆ (s1 ⨝ far)[pId] ⇒ Farmer ⊆ (s2 ⨝ near)[pId])
    ' 
    '// During a transition the boat can only have at max one passenger
    '∀ o ∈ ordering, p1 ∈ Passenger ∖ Farmer, p2 ∈ Passenger ∖ (Farmer ∪ p1) | let s1 = o[cur][cur as sId], s2 = o[next][next as sId] |
    '  (¬ (p1 ∪ p2 ⊆ (s1 ⨝ near)[pId] ∩ (s2 ⨝ far)[pId] ∨ 
    '      p1 ∪ p2 ⊆ (s1 ⨝ far)[pId] ∩ (s2 ⨝ near)[pId]))
    '
    '// If a passengers goes from one side to the other it means that the Farmer also goes from the same side to the other
    '∀ o ∈ ordering, p ∈ (Passenger ∖ Farmer) | let s1 = o[cur][cur as sId], s2 = o[next][next as sId] | 
    '  ( ((p ⊆ ((s1 ⨝ near)[pId] ∩ (s2 ⨝ far)[pId])) ⇒ Farmer ⊆ (s1 ⨝ near)[pId] ∩ (s2 ⨝ far)[pId]) ∧ 
    '    ((p ⊆ (s1 ⨝ far)[pId] ∩ (s2 ⨝ near)[pId]) ⇒ Farmer ⊆ (s1 ⨝ far)[pId] ∩ (s2 ⨝ near)[pId]) )
    '
    '// The Wolf can never be on the same shore then the Goat and the Cabbage can never be on the same shore then the Goat unless the Farmer is there as well
    '∀ s ∈ State, e ∈ eats | let p1 = e[pId], p2 = e[eat][eat as pId] | 
    '   (p1 ⊆ (s ⨝ near)[pId] ∧ p2 ⊆ (s ⨝ far)[pId]) ∨ 
    '   (p1 ⊆ (s ⨝ far)[pId] ∧ p2 ⊆ (s ⨝ near)[pId]) ∨ 
    '   (p1 ∪ p2 ∪ Farmer ⊆ (s ⨝ near)[pId]) ∨ 
    '   (p1 ∪ p2 ∪ Farmer ⊆ (s ⨝ far)[pId])";
