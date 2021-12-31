module benchmark::relational::account::AlleAlleAccountBenchmark

import util::Math;

extend benchmark::AlleAlleBenchmark;

void runAccountBenchmark(str postfix = "") 
  = runBenchmark([5..11], "relational", "account", true, postfix = postfix); 

str constructRels(int config) 
  = "State (sId:id, amount:int)     \>= {\<s1,0\>} \<= {\<s1,0\>,\<s2,?\>..\<s5,?\>}
    'InitialState (sId:id)           = {\<s1\>}
    'ordering (from:id,to:id)       \<= {\<s1,s2\>,\<s2,s3\>,\<s3,s4\>,\<s4,s5\>}
    'Account (aId:id, balance:int)  \>= {\<ac1,?\>} \<= {\<ac1,?\>..\<ac5,?\>}
    'accountInState (sId:id,aId:id) \>= {\<s1,ac1\>} \<= {\<s1,ac1\>,\<s2,ac2\>,\<s3,ac3\>,\<s4,ac4\>,\<s5,ac5\>}
    '
    'Withdraw (eId:id)               = {\<withdraw\>}
    'Deposit (eId:id)                = {\<deposit\>}
    'triggeredEvent (sId:id,eId:id) \<= {\<s2,withdraw\>..\<s5,withdraw\>,\<s2,deposit\>..\<s5,deposit\>}";
    
str getConstraints(int config)
  = "ordering ⊆ State[sId][sId as from] ⨯ State[sId][sId as to]
    'accountInState ⊆ State[sId] ⨯ Account[aId]
    'triggeredEvent ⊆ State[sId] ⨯ (Withdraw ∪ Deposit)
    '
    '// Entity constraints
    '∀ s ∈ State | some s ⨝ accountInState
    '
    'State[sId] ⊆ (InitialState[sId as from] ⨝ *ordering)[to][to as sId]
    'Account[aId] ⊆ ((InitialState[sId as from] ⨝ *ordering)[to][to as sId] ⨝ accountInState)[aId]
    '
    '∀ s ∈ State ∖ (InitialState ⨝ State) |  some (s where amount \> 0 && amount \< <toInt(pow(2,config-3))>)
    '
    '// Initial state
    'some ((InitialState ⨝ accountInState ⨝ Account) where balance = 0)
    '
    '// Transition function
    '∀ o ∈ ordering | let s1 = o[from][from as sId], s2 = o[to][to as sId], 
    '                 b = (s2 ⨝ accountInState ⨝ Account ⨝ State)[balance, amount][balance as newBalance] ⨯ (s1 ⨝ accountInState ⨝ Account)[balance] | 
    ' (
    '   ((some b where newBalance = (balance + amount)) ∧ (s2 ⨝ triggeredEvent)[eId] = Deposit) ∨ 
    '   ((some b where ((balance - amount) \>= 0 && (newBalance = (balance - amount)))) ∧ (s2 ⨝ triggeredEvent)[eId] = Withdraw)
    ' ) 
    '// Goal state 
    '∃ s ∈ State | some (s ⨝ accountInState ⨝ Account) where balance = <toInt(pow(2,config-1)) - config>";
  