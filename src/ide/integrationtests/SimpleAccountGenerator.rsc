module ide::integrationtests::SimpleAccountGenerator

import IO;
import List;

void generateAccountProblem(int goalBalance, int amountLowerBound, int amountUpperBound, int maxDepth, loc output) {
  str problem = "{<intercalate(",", ["s<i>" | int i <- [0..maxDepth]])>,<intercalate(",", ["ac<i>" | int i <- [0..maxDepth]])>,<intercalate(",", ["b<i>(int)" | int i <- [0..maxDepth]])>,<intercalate(",", ["am<i>(int)" | int i <- [1..maxDepth]])>,withdraw, deposit}
                '
                'State: 1 [{\<s0\>},{<intercalate(",", ["\<s<i>\>" | int i <- [0..maxDepth]])>}]
                'InitialState: 1 [{\<s0\>},{\<s0\>}]
                'ordering: 2[{}, {<intercalate(",", ["\<s<i>,s<i+1>\>" | int i <- [0..maxDepth-1]])>}]
                'Account:1 [{\<ac0\>},{<intercalate(",", ["\<ac<i>\>" | int i <- [0..maxDepth]])>}]
                'accountInState:2 [{\<s0,ac0\>},{<intercalate(",", ["\<s<i>,ac<i>\>" | int i <- [0..maxDepth]])>}]
                '
                'Withdraw:1[{\<withdraw\>},{\<withdraw\>}]
                'Deposit:1[{\<deposit\>},{\<deposit\>}]
                'triggeredEvent:2 [{},{<intercalate(",", ["\<s<i>,withdraw\>,\<s<i>,deposit\>" | int i <- [1..maxDepth]])>}]
                '
                'Balance:1 [{\<b0\>}, {<intercalate(",", ["\<b<i>\>" | int i <- [0..maxDepth]])>}]
                'balance:2 [{\<ac0,b0\>}, {<intercalate(",", ["\<ac<i>,b<i>\>" | int i <- [0..maxDepth]])>}]
                '
                'Amount:1[{},{<intercalate(",", ["\<am<i>\>" | int i <- [1..maxDepth]])>}]
                'amount:2[{},{<intercalate(",", ["\<s<i>,am<i>\>" | int i <- [1..maxDepth]])>}]
                '
                'ordering in State -\> State
                'accountInState in State -\> Account 
                'balance in Account -\> Balance
                'amount in State -\> Amount
                '
                'triggeredEvent in State-\>(Withdraw++Deposit)
                '
                'balance[accountInState[InitialState]] = 0
                '
                'forall s:State\\InitialState | some ordering.s
                'forall a:Account | some accountInState.a
                'forall b:Balance | some balance.b
                'forall a:Amount | some amount.a
                '
                'forall s1: State, s2:State | s1 -\> s2 in ordering =\> 
                '  (some balance[accountInState[s2]]) && (some balance[accountInState[s1]]) &&
                '  (some amount[s2]) && (amount[s2]) \> <amountLowerBound> && (amount[s2]) \< <amountUpperBound> &&
                '  (
                '    (balance[accountInState[s2]] = balance[accountInState[s1]] + (amount[s2]) && triggeredEvent[s2] == Deposit) ||
                '    (balance[accountInState[s2]] = balance[accountInState[s1]] - (amount[s2]) && triggeredEvent[s2] == Withdraw)
                '  )
                ' 
                'exists s:State | balance[accountInState[s]] = <goalBalance>";
    
  writeFile(output, problem);    
}

void generateTransferProblem(int maxDepth, loc output) {
  str problem = "{<intercalate(",", ["s<i>" | int i <- [0..maxDepth]])>,<intercalate(",", ["b1_<i>(int)" | int i <- [0..maxDepth]])>,<intercalate(",", ["b2_<i>(int)" | int i <- [0..maxDepth]])>,<intercalate(",", ["a<i>(int)" | int i <- [1..maxDepth]])>}
                '
                'State:1          [{\<s0\>},{<intercalate(",", ["\<s<i>\>" | int i <- [0..maxDepth]])>}]
                'InitialState:1   [{\<s0\>},{\<s0\>}]
                'ordering:2       [{}, {<intercalate(",", ["\<s<i>,s<i+1>\>" | int i <- [0..maxDepth-1]])>}]
                'Balance:1        [{\<b1_0\>,\<b2_0\>},{<intercalate(",", ["\<b1_<i>\>,\<b2_<i>\>" | int i <- [0..maxDepth]])>}]
                'balance1:2       [{\<s0,b1_0\>},{<intercalate(",", ["\<s<i>,b1_<i>\>" | int i <- [0..maxDepth]])>}]
                'balance2:2       [{\<s0,b2_0\>},{<intercalate(",", ["\<s<i>,b2_<i>\>" | int i <- [0..maxDepth]])>}]
                'Amount:1         [{},{<intercalate(",", ["\<a<i>\>" | int i <- [1..maxDepth]])>}]
                'amount:2         [{},{<intercalate(",", ["\<s<i>,a<i>\>" | int i <- [1..maxDepth]])>}]
                '
                'ordering in State-\>State
                'balance1 in State-\>Balance
                'balance2 in State-\>Balance
                'amount   in State-\>Amount
                '
                'forall s:State\\InitialState | some ordering.s
                'forall b:Balance | some balance1.b || some balance2.b
                'forall a:Amount | some amount.a
                '
                'balance1[InitialState] = 100
                'balance2[InitialState] = 100
                '
                'forall s1:State, s2:State | s1-\>s2 in ordering =\>
                '  (some balance1[s1] && some balance1[s2] && some balance2[s1] && some balance2[s2] && some amount[s2]) &&
                '  amount[s2] \> 0 &&
                '  (
                '    (balance1[s1] \> amount[s2] &&
                '     balance1[s2] = (balance1[s1]) - (amount[s2]) &&
                '     balance2[s2] = (balance2[s2]) + (amount[s2])) 
                '    ||
                '    (balance2[s1] \> amount[s2] &&
                '     balance1[s2] = (balance1[s1]) + (amount[s2]) &&
                '     balance2[s2] = (balance2[s1]) - (amount[s2]))    
                '  )
                '
                'exists s:State | balance1[s] \> 200";
                
  writeFile(output, problem);
}