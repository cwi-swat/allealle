module ide::integrationtests::RushHourGenerator

import List;
import IO;

data Direction
  = hor()
  | ver()
  ;

data Vehicle
  = car(Direction dir, int row, int col)
  | redCar(int row, int col)
  | truck(Direction dir, int row, int col)
  ;

alias InitialSetup = map[str name, Vehicle v];
alias Puzzle = tuple[InitialSetup setup, int maxSteps];

Puzzle puzzle1 = <("green_car":car(hor(),0,0), "red_car":redCar(2,1), "blue_car":car(hor(),4,4), "orange_car":car(ver(),4,0), "purple_truck":truck(ver(),1,0), "blue_truck":truck(ver(),1,3), "yellow_truck":truck(ver(),0,5), "green_truck":truck(hor(),5,2)), 2>;
Puzzle puzzle2 = <("green_car":car(ver(),0,0), "yellow_truck":truck(hor(),0,3), "red_car":redCar(2,0), "orange_car":car(ver(),1,3), "blue_car":car(ver(),2,4), "purple_truc":truck(ver(),1,5), "blue_truck":truck(hor(),3,0), "dark_green_car":car(hor(),5,0), "pink_car":car(ver(),4,2), "black_car":car(hor(),5,3), "purple_car":car(hor(),4,4)), 3>;
Puzzle puzzle40 = <("yellow_truck": truck(ver(),0,0), "light_green_car":car(hor(),0,1), "blue_car":car(ver(),1,1), "pink_car":car(ver(),1,2), "orange_car":car(ver(),0,4), "red_car":redCar(2,3), "pink_truck":truck(ver(),1,5), "blue_truck":truck(hor(),3,0), "purple_car":car(ver(),3,3), "brown_car":car(hor(),5,0), "dark_green_car":car(ver(),4,2), "yellow_car":car(hor(),5,3), "black_car":car(hor(),4,4)), 10>;

void genProblem1() = genProblem(puzzle1);
void genProblem2() = genProblem(puzzle2);
void genProblem40() = genProblem(puzzle40);


void genProblem(Puzzle p) {
  str problem = constructProblem(p.setup, p.maxSteps);
  
  writeFile(|project://allealle/examples/intOpt/rushhour.alle|, problem);
}

str constructProblem(InitialSetup setup, int maxSteps) {
  str genVehicleRel() = intercalate(",", ["\<<n>,<length>\>" | str n <- setup, int length := ((truck(_,_,_) := setup[n]) ? 3 : 2)]);
  str genRedCarRel() = "\<<n>\>" when str n <- setup, redCar(_,_) := setup[n]; 
  str genHorizontalRel() = intercalate(",", ["\<<n>\>" | str n <- setup, redCar(_,_) := setup[n] || (setup[n] has dir && setup[n].dir == hor())]);
  str genVerticalRel() = intercalate(",", ["\<<n>\>" | str n <- setup, setup[n] has dir && setup[n].dir == ver()]);

  str genStateRel() = intercalate(",", ["\<s<i>\>" | int i <- [1..maxSteps+2]]);
  str genOrdeningRel() = intercalate(",", ["\<s<i>,s<i+1>\>" | int i <- [1..maxSteps+1]]);
  
  str genPosInState(str name, Vehicle v, 1) = "\<s1,<name>,<v.row>,<v.col>\>"; 
  str genPosInState(str name, Vehicle v, int step) = "\<s<step>,<name>,<v.row>,?\>" when step > 1, redCar(_,_) := v || car(hor(),_,_) := v || truck(hor(),_,_) := v; 
  str genPosInState(str name, Vehicle v, int step) = "\<s<step>,<name>,?,<v.col>\>" when step > 1, car(ver(),_,_) := v || truck(ver(),_,_) := v; 
  str genPosInStateRel(int limit) = intercalate(",", [genPosInState(n, setup[n], i) | str n <- setup, int i <- [1..limit]]);
  
  return "
         'Vehicle (1 :: length:int)             = {<genVehicleRel()>}
         'RedCar (1)                            = {<genRedCarRel()>}
         'Horizontal (1)                        = {<genHorizontalRel()>}
         'Vertical (1)                          = {<genVerticalRel()>}
         '
         'State (1)                             \>={\<s1\>} \<= {<genStateRel()>}
         'InitialState (1)                      = {\<s1\>}
         'ordening (2)                         \<= {<genOrdeningRel()>}
         '
         'posInState (2 :: row:int, col:int)  \>= {<genPosInStateRel(2)>} \<= {<genPosInStateRel(maxSteps+2)>}
         '
         'ordening in State-\>State
         'posInState in State-\>Vehicle
         '
         '// all states should be reachable from the initial state
         'forall s:State | s in InitialState.*ordening
         '
         '// All vehicles have a position in every state
         'State-\>Vehicle in posInState
         '
         'forall v:Horizontal | let p:State-\>v | p::col \>= 0 && p::col \<= (6 - v::length)
         'forall v:Vertical   | let p:State-\>v | p::row \>= 0 && p::row \<= (6 - v::length)
         '
         '// goal is to get the red car out
         'exists s:State |  (s-\>RedCar)::col = 4
         '
         '// two horizontal cars on the same row should never overlap
         'forall s:State, v1:Horizontal, v2:Horizontal\\v1 | let p1:s-\>v1, p2:s-\>v2 | 
         '  p1::row = p2::row =\>  
         '    (p1::col \<= p2::col =\> (p2::col - p1::col \>= v1::length)) &&
         '    (p1::col \>  p2::col =\> (p1::col - p2::col \>= v2::length))
         '  
         '// two vertical cars in the same column should never overlap
         'forall s:State, v1:Vertical, v2:Vertical\\v1 | let p1:s-\>v1, p2:s-\>v2 | 
         '  p1::col = p2::col =\>  
         '    (p1::row \<= p2::row =\> (p2::row - p1::row \>= v1::length)) &&
         '    (p1::row \>  p2::row =\> (p1::row - p2::row \>= v2::length))
         '    
         '// two cars with orthogonal directions should never overlap
         'forall s:State, v1:Horizontal, v2:Vertical | let p1:s-\>v1, p2:s-\>v2 | 
         '  (p1::col \<= p2::col && ((p2::col - p1::col) \< v1::length) =\> (p1::row \< p2::row || (p1::row - p2::row) \>= v2::length)) 
         '
         '// two horizontal cars on the same row can not bunny hop over eachother
         'forall s1:State, s2:State, v1:Horizontal, v2:Horizontal\\v1 | s1-\>s2 in ordening =\> (let p1Old:s1-\>v1, p1New:s2-\>v1, p2Old:s1-\>v2, p2New:s2-\>v2 |
         '  p1Old::row = p2Old::row =\> ((p1Old::col \< p2Old::col =\> p1New::col \< p2New::col) && 
         '                               (p1Old::col \> p2Old::col =\> p1New::col \> p2New::col)))
         '
         '// two vertical cars on the same column can not bunny hop over eachother
         'forall s1:State, s2:State, v1:Vertical, v2:Vertical\\v1 | s1-\>s2 in ordening =\> (let p1Old:s1-\>v1, p1New:s2-\>v1, p2Old:s1-\>v2, p2New:s2-\>v2 |
         '  p1Old::col = p2Old::col =\> ((p1Old::row \< p2Old::row =\> p1New::row \< p2New::row) &&
         '                               (p1Old::row \> p2Old::row =\> p1New::row \> p2New::row)))
         '
         '// two orthogonal vehicles can not bunny hop over eachother
         'forall s1:State, s2:State, v1:Horizontal, v2:Vertical | s1-\>s2 in ordening =\> (let p1Old:s1-\>v1, p1New:s2-\>v1, p2Old:s1-\>v2, p2New:s2-\>v2 |
         '  // horziontal v1 hops over vertical v2
         '  ((p1Old::col \< p2Old::col && p1New::col \> p2New::col && p1Old::row \>= p2Old::row && p1Old::row \< (p2Old::row + v2::length)) =\> (p2New::row \> p1New::row || (p2New::row + v2::length) \<= p1New::row )) &&
         '  ((p1Old::col \> p2Old::col && p1New::col \< p2New::col && p1Old::row \>= p2Old::row && p1Old::row \< (p2Old::row + v2::length)) =\> (p2New::row \> p1New::row || (p2New::row + v2::length) \<= p1New::row )) &&
         '  // vertical v2 hops over horizontal v1
         '  ((p2Old::row \< p1Old::row && p2New::row \> p1New::row && p2Old::col \>= p1Old::col && p2Old::col \< (p1Old::col + v1::length)) =\> (p1New::col \> p2New::col || (p1New::col + v1::length) \<= p2New::col)) &&
         '  ((p2Old::row \> p1Old::row && p2New::row \< p1New::row && p2Old::col \>= p1Old::col && p2Old::col \< (p1Old::col + v1::length)) =\> (p1New::col \> p2New::col || (p1New::col + v1::length) \<= p2New::col)) )
         ' 
         'minimize #State
         ";
}