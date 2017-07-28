module ide::integrationtests::RushHourGenerator

import List;
import IO;

data Direction
  = hor()
  | ver()
  ;

data Vehicle
  = car(Direction dir, int row, int col)
  | redCar(int col)
  | truck(Direction dir, int row, int col)
  ;

alias InitialSetup = map[str name, Vehicle v];
alias Puzzle = tuple[InitialSetup setup, int maxSteps];

Puzzle puzzle1 = <("green_car":car(hor(),0,0), "red_car":redCar(1), "blue_car":car(hor(),4,4), "orange_car":car(ver(),4,0), "purple_truck":truck(ver(),1,0), "blue_truck":truck(ver(),1,3), "yellow_truck":truck(ver(),0,5), "green_truck":truck(hor(),5,2)), 8>;
Puzzle puzzle2 = <("green_car":car(ver(),0,0), "yellow_truck":truck(hor(),0,3), "red_car":redCar(0), "orange_car":car(ver(),1,3), "blue_car":car(ver(),2,4), "purple_truc":truck(ver(),1,5), "blue_truck":truck(hor(),3,0), "darg_green_car":car(hor(),5,0), "pink_car":car(ver(),4,2), "black_car":car(hor(),5,3), "purple_car":car(hor(),4,4)), 8>;
Puzzle puzzle40 = <("yt": truck(ver(),0,0), "lgc":car(hor(),0,1), "bluc":car(ver(),1,1), "pic":car(ver(),1,2), "oc":car(ver(),0,4), "rc":redCar(3), "pt":truck(ver(),1,5), "bt":truck(hor(),3,0), "puc":car(ver(),3,3), "brc":car(hor(),5,0), "dgc":car(ver(),4,2), "yc":car(hor(),5,3), "bla":car(hor(),4,4)), 5>;

void genProblem1() = genProblem(puzzle1);
void genProblem2() = genProblem(puzzle2);
void genProblem40() = genProblem(puzzle40);


void genProblem(Puzzle p) {
  str problem = constructProblem(p.setup, p.maxSteps);
  
  writeFile(|project://allealle/examples/intOpt/rushhour.alle|, problem);
}

str constructProblem(InitialSetup setup, int maxSteps) {

  str genPosUniverseTuple(str name, redCar(int col), 1)     = "<name>_ps1{row(int)=2,col(int)=<col>}"; 
  str genPosUniverseTuple(str name, redCar(int col), int i) = "<name>_ps<i>{row(int)=2,col(int)}" when i > 1; 
  str genPosUniverseTuple(str name, Vehicle v, 1)           = "<name>_ps1{row(int)=<v.row>,col(int)=<v.col>}" when redCar(_) !:= v; 
  str genPosUniverseTuple(str name, Vehicle v, int i)       = "<name>_ps<i>{row(int),col(int)=<v.col>}" when redCar(_) !:= v, v.dir == ver(), i > 1; 
  str genPosUniverseTuple(str name, Vehicle v, int i)       = "<name>_ps<i>{row(int)=<v.row>,col(int)}" when redCar(_) !:= v, v.dir == hor(), i > 1; 

  str genPosUniverseTuples(str name, Vehicle v) = intercalate(",", [genPosUniverseTuple(name, v, i) | int i <- [1..maxSteps+2]]);
  str genAllPosTuples() = intercalate(",\n", [genPosUniverseTuples(name, setup[name]) | str name <- setup]); 
                          
  str genVehicleTuple(str name, car(_,_,_)) = "<name>{length(int)=2}";
  str genVehicleTuple(str name, truck(_,_,_)) = "<name>{length(int)=3}";
  str genVehicleTuple(str name, redCar(_)) = "<name>{length(int)=2}";
  str genVehicleTuples() = intercalate(",", [genVehicleTuple(name, setup[name]) | str name <- setup]);
  
  str genStateAtoms() = intercalate(",", ["s<i>" | int i <- [1..maxSteps+2]]);
  
  str genVehicleRel() = intercalate(",", ["\<<n>\>" | str n <- setup]);
  str genRedCarRel() = "\<<n>\>" when str n <- setup, redCar(_) := setup[n]; 
  str genHorizontalRel() = intercalate(",", ["\<<n>\>" | str n <- setup, redCar(_) := setup[n] || (setup[n] has dir && setup[n].dir == hor())]);
  str genVerticalRel() = intercalate(",", ["\<<n>\>" | str n <- setup, setup[n] has dir && setup[n].dir == ver()]);

  str genStateRel() = intercalate(",", ["\<s<i>\>" | int i <- [1..maxSteps+2]]);
  str genOrdeningRel() = intercalate(",", ["\<s<i>,s<i+1>\>" | int i <- [1..maxSteps+1]]);
  
  str genPosRel(int limit) = intercalate(",", ["\<<n>_ps<i>\>" | str n <- setup, int i <- [1..limit]]); 
  str genPosInStateRel(int limit) = intercalate(",", ["\<s<i>,<n>,<n>_ps<i>\>" | str n <- setup, int i <- [1..limit]]);
  
  return "{<genVehicleTuples()>,
         ' <genStateAtoms()>,  
         ' <genAllPosTuples()>}
         '
         'Vehicle:1     [{<genVehicleRel()>},{<genVehicleRel()>}]
         'RedCar:1      [{<genRedCarRel()>},{<genRedCarRel()>}]
         'Horizontal:1  [{<genHorizontalRel()>},{<genHorizontalRel()>}]
         'Vertical:1    [{<genVerticalRel()>},{<genVerticalRel()>}]
         '
         'State:1       [{\<s1\>},{<genStateRel()>}]
         'InitialState:1[{\<s1\>},{\<s1\>}]
         'ordening:2    [{},{<genOrdeningRel()>}]
         '
         'Position:1    [{<genPosRel(2)>},{<genPosRel(maxSteps+2)>}]
         'posInState:3  [{<genPosInStateRel(2)>},{<genPosInStateRel(maxSteps+2)>}]
         '
         'ordening in State-\>State
         'posInState in State-\>Vehicle-\>Position
         '
         '// all states should be reachable from the initial state
         'forall s:State | s in InitialState.*ordening
         '
         '// All vehicles have a position in every state
         'forall s:State, v:Vehicle | some v.(s.posInState)
         '// There are not more positions then there are vehicles in states
         'Position in Vehicle.(State.posInState) 
         '
         'forall v:Horizontal | let p:v.(State.posInState) | p::col \>= 0 && p::col \<= (6 - v::length)
         'forall v:Vertical   | let p:v.(State.posInState) | p::row \>= 0 && p::row \<= (6 - v::length)
         '
         '// goal is to get the red car out
         'exists s:State |  (RedCar.(s.posInState))::col = 4
         '
         '// some vehicle should move between two states
         'forall s1:State, s2:State\\s1 | s1-\>s2 in ordening =\>
         '    let moved:{v:Vehicle | let pOld:v.(s1.posInState), pNew:v.(s2.posInState) | pOld::col != pNew::col || pOld::row != pNew::row} | #moved = 1
         '////  (exists v:Vehicle | let pOld:v.(s1.posInState), pNew:v.(s2.posInState) | pOld::col != pNew::col || pOld::row != pNew::row)
         ' 
         '// two horizontal cars on the same row should never overlap
         'forall s:State, v1:Horizontal, v2:Horizontal\\v1 | let p1:v1.(s.posInState), p2:v2.(s.posInState) | 
         '  p1::row = p2::row =\>  
         '    (p1::col \<= p2::col =\> (p2::col - p1::col \>= v1::length)) &&
         '    (p1::col \>  p2::col =\> (p1::col - p2::col \>= v2::length))
         ' 
         '// two vertical cars in the same column should never overlap
         'forall s:State, v1:Vertical, v2:Vertical\\v1 | let p1:v1.(s.posInState), p2:v2.(s.posInState) | 
         '  p1::col = p2::col =\>  
         '    (p1::row \<= p2::row =\> (p2::row - p1::row \>= v1::length)) &&
         '    (p1::row \>  p2::row =\> (p1::row - p2::row \>= v2::length))
         '   
         '// two cars with orthogonal directions should never overlap
         'forall s:State, v1:Horizontal, v2:Vertical | let p1:v1.(s.posInState), p2:v2.(s.posInState) | 
         '  (p1::col \<= p2::col && ((p2::col - p1::col) \< v1::length) =\> (p1::row \< p2::row || (p1::row - p2::row) \>= v2::length)) 
         '
         '// two horizontal cars on the same row can not bunny hop over eachother
         'forall s1:State, s2:State, v1:Horizontal, v2:Horizontal\\v1 | s1-\>s2 in ordening =\> (let p1Old:v1.(s1.posInState), p1New:v1.(s2.posInState), p2Old:v2.(s1.posInState), p2New:v2.(s2.posInState) |
         '  p1Old::row == p2Old::row =\> ((p1Old::col \< p2Old::col =\> p1New::col \< p2New::col) && 
         '                               (p1Old::col \> p2Old::col =\> p1New::col \> p2New::col)))
         '
         '// two vertical cars on the same column can not bunny hop over eachother
         'forall s1:State, s2:State, v1:Vertical, v2:Vertical\\v1 | s1-\>s2 in ordening =\> (let p1Old:v1.(s1.posInState), p1New:v1.(s2.posInState), p2Old:v2.(s1.posInState), p2New:v2.(s2.posInState) |
         '  p1Old::col == p2Old::col =\> ((p1Old::row \< p2Old::row =\> p1New::row \< p2New::row) && 
         '                               (p1Old::row \> p2Old::row =\> p1New::row \> p2New::row)))
         '
         '// two orthogonal vehicles can not bunny hop over eachother
         'forall s1:State, s2:State, v1:Horizontal, v2:Vertical | s1-\>s2 in ordening =\> (let p1Old:v1.(s1.posInState), p1New:v1.(s2.posInState), p2Old:v2.(s1.posInState), p2New:v2.(s2.posInState) |
         '  ((p1Old::col \< p2Old::col && p1New::col \> p2Old::col) =\> ((p1Old::row \< p2Old::row || p1Old::row \>= (p2Old::row + v2::length)))) &&
         '  ((p1Old::col \> p2Old::col && p1New::col \< p2Old::col) =\> ((p1Old::row \< p2Old::row || p1Old::row \>= (p2Old::row + v2::length)))) &&
         '  ((p2Old::row \< p1Old::row && p2New::row \> p1New::row) =\> ((p2Old::col \< p1Old::col || p2Old::col \>= (p1Old::col + v1::length)))) &&
         '  ((p2Old::row \> p1Old::row && p2New::row \< p1New::row) =\> ((p2Old::col \< p1Old::col || p2Old::col \>= (p1Old::col + v1::length)))))  
         '
         'minimize #State";
}