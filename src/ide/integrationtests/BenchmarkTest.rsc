module ide::integrationtests::BenchmarkTest

import ide::Imploder;
import ide::CombinedAST;
import ide::CombinedModelFinder;

import IO;
import List;

//{s0,s1,s2,b1_1{balance(int)},b1_2{balance(int)},b1_3{balance(int)},b2_1{balance(int)},b2_2{balance(int)},b2_3{balance(int)},a1{val(int)},a2{val(int)}}
//
//State:1         [{<s0>},{<s0>,<s1>,<s2>}]
//InitialState:1  [{<s0>},{<s0>}]
//ordering:2      [{},{<s0,s1>,<s1,s2>}]
//
//account1:2      [{},{<s0,b1_1>,<s1,b1_2>,<s2,b1_3>}]
//account2:2      [{},{<s0,b2_1>,<s1,b2_2>,<s2,b2_3>}]
//amount:2        [{},{<s1,a1>,<s2,a2>}]
//
//ordering in State->State
//InitialState in State
//
//forall s:State\InitialState | some ordering.s 
//
//forall s:State | some account1[s] && some account2[s]
//forall s:State | some ordering.s => some amount[s]
//
//forall am:amount | some State.am
//forall a:account1 | some State.a
//forall a:account2 | some State.a
//
//account1[InitialState]::balance = 100
//account2[InitialState]::balance = 100
//
//forall s1:State, s2:State | s1->s2 in ordering =>
//  amount[s2]::val > 0 &&
//
//  ((account1[s1]::balance > amount[s2]::val &&
//   account1[s2]::balance = (account1[s1]::balance) - (amount[s2]::val) &&
//   account2[s2]::balance = (account2[s1]::balance) + (amount[s2]::val)) ||
//
//  (account2[s1]::balance > amount[s2]::val &&
//   account1[s2]::balance = (account1[s1]::balance) + (amount[s2]::val) &&
//   account2[s2]::balance = (account2[s1]::balance) - (amount[s2]::val)))    
//
//exists s:State | account1[s]::balance = 199

void runBenchmark() {
  str problem = generateUnsatTransferProblem(20);
  
  writeFile(|project://allealle/benchmark/latest.alle|, problem);
}

str generateUnsatTransferProblem(int maxDepth) =
  "{<intercalate(",", ["s<i>" | int i <- [0..maxDepth]])>,
  ' <intercalate(",", ["ac1_<i>{balance(int)}" | int i <- [0..maxDepth]])>,
  ' <intercalate(",", ["ac2_<i>{balance(int)}" | int i <- [0..maxDepth]])>,
  ' <intercalate(",", ["am<i>{val(int)}" | int i <- [1..maxDepth]])>}
  '
  'State:1          [{\<s0\>},{<intercalate(",", ["\<s<i>\>"   | int i <- [0..maxDepth]])>}]
  'InitialState:1   [{\<s0\>},{\<s0\>}]
  'ordering:2       [{}, {<intercalate(",", ["\<s<i>,s<i+1>\>" | int i <- [0..maxDepth-1]])>}]
  '
  'account1:2       [{},{<intercalate(",", ["\<s<i>,ac1_<i>\>" | int i <- [0..maxDepth]])>}]
  'account2:2       [{},{<intercalate(",", ["\<s<i>,ac2_<i>\>" | int i <- [0..maxDepth]])>}]
  'amount:2         [{},{<intercalate(",", ["\<s<i>,am<i>\>"   | int i <- [1..maxDepth]])>}]
  'ordering in State-\>State
  'InitialState in State
  '
  'forall s:State\\InitialState | some ordering.s 
  '
  'forall s:State | some account1[s] && some account2[s]
  'forall s:State | some ordering.s =\> some amount[s]
  '
  'forall am:amount | some State.am
  'forall a:account1 | some State.a
  'forall a:account2 | some State.a
  '
  'account1[InitialState]::balance = 100
  'account2[InitialState]::balance = 100
  '
  'forall s1:State, s2:State | s1-\>s2 in ordering =\>
  '  amount[s2]::val \> 0 &&
  '
  '  ((account1[s1]::balance \> amount[s2]::val &&
  '   account1[s2]::balance = (account1[s1]::balance) - (amount[s2]::val) &&
  '   account2[s2]::balance = (account2[s1]::balance) + (amount[s2]::val)) ||
  '
  '  (account2[s1]::balance \> amount[s2]::val &&
  '   account1[s2]::balance = (account1[s1]::balance) + (amount[s2]::val) &&
  '   account2[s2]::balance = (account2[s1]::balance) - (amount[s2]::val)))    
  '
  'exists s:State | account1[s]::balance = 200
  ";
