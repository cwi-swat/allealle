module ide::integrationtests::BenchmarkTest

import ide::Imploder;
import ide::CombinedAST;
import ide::CombinedModelFinder;

import IO;
import List;

void runBenchmark() {
  str problem = generateUnsatAlleAlleTransferProblem(20);
  
  writeFile(|project://allealle/benchmark/latest.alle|, problem);
}

str generateUnsatAlleAlleTransferProblem(int maxDepth) =
  "{<intercalate(",", ["s<i>" | int i <- [0..maxDepth]])>,
  ' <intercalate(",", ["ac1_<i>{balance(int)}" | int i <- [0..maxDepth]])>,
  ' <intercalate(",", ["ac2_<i>{balance(int)}" | int i <- [0..maxDepth]])>,
  ' <intercalate(",", ["am<i>{val(int)}" | int i <- [1..maxDepth]])>}
  '
  'State:1          [{\<s0\>},{<intercalate(",", ["\<s<i>\>"   | int i <- [0..maxDepth]])>}]
  'InitialState:1   [{\<s0\>},{\<s0\>}]
  'ordering:2       [{}, {<intercalate(",", ["\<s<i>,s<i+1>\>" | int i <- [0..maxDepth-1]])>}]
  '
  'account1InState:2  [{},{<intercalate(",", ["\<s<i>,ac1_<i>\>" | int i <- [0..maxDepth]])>}]
  'account2InState:2  [{},{<intercalate(",", ["\<s<i>,ac2_<i>\>" | int i <- [0..maxDepth]])>}]
  'paramsInState:2    [{},{<intercalate(",", ["\<s<i>,am<i>\>"   | int i <- [1..maxDepth]])>}]
  '
  'ordering in State-\>State
  'InitialState in State
  '
  'forall s:State\\InitialState | some ordering.s 
  '
  'forall s:State | some account1InState[s] && some account2InState[s]
  'forall s:State | some ordering.s =\> some paramsInState[s]
  '
  'forall p:paramsInState | some State.p
  'forall a:account1InState | some State.a
  'forall a:account2InState | some State.a
  '
  'account1InState[InitialState]::balance = 100
  'account2InState[InitialState]::balance = 100
  '
  'forall s1:State, s2:State | s1-\>s2 in ordering =\>
  '  paramsInState[s2]::val \> 0 &&
  '
  '  ((account1InState[s1]::balance \> paramsInState[s2]::val &&
  '   account1InState[s2]::balance = (account1InState[s1]::balance) - (paramsInState[s2]::val) &&
  '   account2InState[s2]::balance = (account2InState[s1]::balance) + (paramsInState[s2]::val)) ||
  '
  '  (account2InState[s1]::balance \> paramsInState[s2]::val &&
  '   account1InState[s2]::balance = (account1InState[s1]::balance) + (paramsInState[s2]::val) &&
  '   account2InState[s2]::balance = (account2InState[s1]::balance) - (paramsInState[s2]::val)))    
  '
  'exists s:State | account1InState[s]::balance = 200
  ";
  
 str generateUnsatSMTTransferProblem(int maxDepth) =
  "(declare-sort State)
  '(declare-fun balance1 (State) Int)
  '(declare-fun balance2 (State) Int)
  '(declare-fun amount (State) Int)
  '
  '(define-fun from1To2 ((current State) (next State)) Bool
  '  (and
  '    (\>= (balance1 current) (amount current)) ; guard
  '    
  '    
  '    (= (- (balance1 current) (amount current)) (balance1 next))
  '    (= (+ (balance2 current) (amount current)) (balance2 next))
  '    (\> (amount next) 0)
  '  )    
  ') 
  '(define-fun from2To1 ((current State) (next State)) Bool
  '  (and
  '    (\>= (balance2 current) (amount current)) ; guard
  '        
  '    (= (+ (balance1 current) (amount current)) (balance1 next))
  '    (= (- (balance2 current) (amount current)) (balance2 next))
  '    (\> (amount next) 0)
  '  )    
  ') 
  '(define-fun transition ((current State) (next State)) Bool
  '  (or 
  '    (from1To2 current next) 
  '    (from2To1 current next)
  '  ) 
  ')
  '(define-fun initial ((state State)) Bool
  '  (and
  '    (= (balance1 state) 100)
  '    (= (balance2 state) 100)
  '    (\> (amount state) 0)
  '  )  
  ')
  '(define-fun goal ((state State)) Bool
  '  (\> (balance1 state) 200) 
  ')
  '<for (int i <- [0..maxDepth]) {>
  '(declare-const S<i> State)<}>
  '
  '(assert 
  '  (and
  '    (initial S0)
  '    (or <for (int i <- [1..maxDepth]) {>
  '      (and <for (int j <- [0..i]) {> (transition S<j> S<j+1>) <}> (goal S<i>))<}>
  '    )
  '  )
  ')
  '
  '(check-sat)"; 
