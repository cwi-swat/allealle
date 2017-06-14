module ide::integrationtests::KillerSudokuGenerator

import IO;
import List;

 
void generateEasyKillerSudoku() { 
  list[Region] regions = [<[<1,1>,<1,2>], 10>,
                          <[<1,3>,<1,4>,<1,5>], 22>,
                          <[<1,6>,<1,7>], 8>,
                          <[<1,8>,<2,8>], 10>,
                          <[<1,9>,<2,9>], 8>,
                          <[<2,1>,<2,2>], 10>,
                          <[<2,3>,<2,4>,<2,5>], 9>,
                          <[<2,6>,<2,7>,<3,7>], 19>,
                          <[<3,1>], 2>,
                          <[<3,2>,<3,3>], 13>,
                          <[<3,4>,<3,5>], 5>,
                          <[<3,6>,<4,6>], 7>,
                          <[<3,8>,<3,9>], 16>,
                          <[<4,1>,<4,2>], 10>,
                          <[<4,3>], 2>,
                          <[<4,4>,<5,4>,<4,5>], 13>,
                          <[<4,7>,<5,7>], 15>,
                          <[<4,8>,<4,8>], 9>,
                          <[<5,1>], 6>,
                          <[<5,2>,<5,3>], 8>,
                          <[<5,5>,<6,5>], 11>,
                          <[<5,6>], 2>,
                          <[<5,8>,<5,9>], 13>,
                          <[<6,1>,<7,1>], 13>,
                          <[<6,2>,<7,2>,<8,2>], 20>,
                          <[<6,3>,<6,4>], 16>,
                          <[<6,6>], 6>,
                          <[<6,7>], 2>,
                          <[<6,8>,<6,9>], 6>,
                          <[<7,3>,<8,3>], 14>,
                          <[<7,4>,<8,4>], 9>,
                          <[<7,5>,<8,5>], 13>,
                          <[<7,6>,<8,6>], 9>,
                          <[<7,7>,<7,8>], 4>,
                          <[<7,9>], 4>,
                          <[<8,1>,<9,1>], 4>,
                          <[<8,7>,<9,7>], 14>,
                          <[<8,8>,<9,8>], 13>,
                          <[<8,9>,<9,9>], 10>,
                          <[<9,2>,<9,3>], 6>,
                          <[<9,4>], 3>,
                          <[<9,5>,<9,6>], 11>
                          ];
  
  // http://www.killersudoku.nl/killer.php?ster=1&nr=1&grootte=2
  generateKillerSudoku(regions, [], |project://allealle/examples/int|);
}   

alias Region = tuple[lrel[int,int] cells, int total];

void generateKillerSudoku(list[Region] regions, lrel[int,int,int] fixedCellValues, loc locationToSave) {
  str gridBound = intercalate(",", ["\<n<c>,n<r>,c<c>_<r>\>" | int c <- [1..10], int r <- [1..10]]);
  
  str buildRegionBound(Region r) = intercalate(", ", ["\<c<c>_<ro>\>" | <int c, int ro> <- r.cells]);
  str buildRegionSumConstraint(Region r, int nr) = "sum(region<nr>) = <r.total>"; //"forall <intercalate(", ", ["c<i>:region<nr><buildUniqueElementCons(i)>" | int i <- [0..size(r.cells)]])> | <intercalate(" + ", ["c<i>" | int i <- [0..size(r.cells)]])> = <r.total>";
  str buildUniqueElementCons(0) = "";
  default str buildUniqueElementCons(int i) = "\\(<intercalate("++", ["c<j>" | int j <- [0..i]])>)";
  
  str problem = "{n1,n2,n3,n4,n5,n6,n7,n8,n9,<intercalate(",",["c<c>_<r>(int)" | int c <- [1..10], int r <- [1..10]])>}
                '
                'num: 1 [{\<n1\>,\<n2\>,\<n3\>,\<n4\>,\<n5\>,\<n6\>,\<n7\>,\<n8\>,\<n9\>},{\<n1\>,\<n2\>,\<n3\>,\<n4\>,\<n5\>,\<n6\>,\<n7\>,\<n8\>,\<n9\>}]
                'cell:1 [{<intercalate(",", ["\<c<c>_<r>\>" | int c <- [1..10], int r <- [1..10]])>},{<intercalate(",", ["\<c<c>_<r>\>" | int c <- [1..10], int r <- [1..10]])>}]
                'r1:  1 [{\<n1\>,\<n2\>,\<n3\>},{\<n1\>,\<n2\>,\<n3\>}]
                'r2:  1 [{\<n4\>,\<n5\>,\<n6\>},{\<n4\>,\<n5\>,\<n6\>}]
                'r3:  1 [{\<n7\>,\<n8\>,\<n9\>},{\<n7\>,\<n8\>,\<n9\>}]
                'grid:3 [{<gridBound>},{<gridBound>}]
                '
                '<for (int i <- [0..size(regions)]) { Region r = regions[i];>
                'region<i>: 1 [{<buildRegionBound(r)>},{<buildRegionBound(r)>}]<}>
                '                
                'r1 in num
                'r2 in num
                'r3 in num
                'grid in num-\>num-\>cell
                '
                'cell \> 0 && cell \< 10
                '
                'forall x:num, y:num  | grid[x][y] != grid[x][num\\y]
                'forall x:num, y:num  | grid[x][y] != grid[num\\x][y]
                'forall x: r1, y: r1  | grid[x][y] != grid[r1\\x][r1\\y]
                'forall x: r1, y: r2  | grid[x][y] != grid[r1\\x][r2\\y]
                'forall x: r1, y: r3  | grid[x][y] != grid[r1\\x][r3\\y]
                'forall x: r2, y: r1  | grid[x][y] != grid[r2\\x][r1\\y]
                'forall x: r2, y: r2  | grid[x][y] != grid[r2\\x][r2\\y]
                'forall x: r2, y: r3  | grid[x][y] != grid[r2\\x][r3\\y]
                'forall x: r3, y: r1  | grid[x][y] != grid[r3\\x][r1\\y]              
                'forall x: r3, y: r2  | grid[x][y] != grid[r3\\x][r2\\y]               
                'forall x: r3, y: r3  | grid[x][y] != grid[r3\\x][r3\\y]
                '
                '<for (int i <- [0..size(regions)]) { Region r = regions[i];>
                '<buildRegionSumConstraint(r, i)><}>
                ";
  
  writeFile(locationToSave + "killersudoku.alle", problem);
  println("done defining the integer sudoku puzzle");
}