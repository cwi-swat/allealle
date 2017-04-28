module ide::integrationtests::SudokuGenerator

import IO;
import List;

void generateKodkodSudoku() {
  rel[int,int,int] puzzle = {<1,1,6>,<1,4,2>,<1,8,5>,<2,2,1>,<2,3,8>,<2,5,6>,<2,8,2>,<3,3,3>,<3,7,4>,<4,4,6>,<4,6,7>,<4,7,8>,<5,1,4>,<5,3,2>,<5,5,5>,
                             <6,4,9>,<6,6,8>,<7,1,5>,<7,3,4>,<7,5,9>,<7,7,3>,<8,2,2>,<8,8,1>,<8,9,4>,<9,1,3>,<9,6,5>,<9,9,7>};
  
//  generateRelSudoku(puzzle, |project://allealle/examples/relational|);
  generateIntSudoku(puzzle, |project://allealle/examples/int|);
}
 
void generateHardSudoku() =  
  // http://www.websudoku.com/?level=3&set_id=9139816530
  generateRelSudoku({<1,1,2>,<1,2,6>,<1,6,9>,<1,8,3>,<2,3,1>,<2,6,2>,<2,7,5>,<3,5,8>,<3,9,6>,<4,2,7>,<4,4,8>,<4,5,6>,<5,4,9>,<5,6,4>,
                  <6,5,5>,<6,6,3>,<6,8,4>,<7,1,9>,<7,5,7>,<8,3,3>,<8,4,2>,<8,7,9>,<9,2,2>,<9,4,4>,<9,8,8>,<9,9,1>}, 
                 |project://allealle/examples/|);   

void generateRelSudoku(rel[int, int, int] filledInCells, loc locationToSave) {
  list[int] getContent(int x, int y) = [content] when <x,y,int content> <- filledInCells;
  default list[int] getContent(int _, int _) = [i | i <- [1..10]]; 
  
  str lb = intercalate(",", ["\<n<x>,n<y>,n<content>\>" | <x,y,content> <- filledInCells]);
  str ub = intercalate(",", ["\<n<x>,n<y>,n<content>\>" | int x <- [1..10], int y <- [1..10], int content <- getContent(x,y)]);
   
  str problem = "{n1,n2,n3,n4,n5,n6,n7,n8,n9}
                '
                'num: 1 [{\<n1\>,\<n2\>,\<n3\>,\<n4\>,\<n5\>,\<n6\>,\<n7\>,\<n8\>,\<n9\>},{\<n1\>,\<n2\>,\<n3\>,\<n4\>,\<n5\>,\<n6\>,\<n7\>,\<n8\>,\<n9\>}]
                'r1:  1 [{\<n1\>,\<n2\>,\<n3\>},{\<n1\>,\<n2\>,\<n3\>}]
                'r2:  1 [{\<n4\>,\<n5\>,\<n6\>},{\<n4\>,\<n5\>,\<n6\>}]
                'r3:  1 [{\<n7\>,\<n8\>,\<n9\>},{\<n7\>,\<n8\>,\<n9\>}]
                'grid:3 [{<lb>},{<ub>}]
                '
                'forall x:num, y: num | some grid[x][y]
                'forall x:num, y: num | no (grid[x][y] & grid[x][num\\y])
                'forall x:num, y: num | no (grid[x][y] & grid[num\\x][y])
                'forall x: r1, y: r1  | no (grid[x][y] & grid[r1\\x][r1\\y])
                'forall x: r1, y: r2  | no (grid[x][y] & grid[r1\\x][r2\\y])
                'forall x: r1, y: r3  | no (grid[x][y] & grid[r1\\x][r3\\y])
                'forall x: r2, y: r1  | no (grid[x][y] & grid[r2\\x][r1\\y])
                'forall x: r2, y: r2  | no (grid[x][y] & grid[r2\\x][r2\\y])
                'forall x: r2, y: r3  | no (grid[x][y] & grid[r2\\x][r3\\y])
                'forall x: r3, y: r1  | no (grid[x][y] & grid[r3\\x][r1\\y])                
                'forall x: r3, y: r2  | no (grid[x][y] & grid[r3\\x][r2\\y])                
                'forall x: r3, y: r3  | no (grid[x][y] & grid[r3\\x][r3\\y])                
                ";
                
   writeFile(locationToSave + "sudoku.alle", problem);
   println("done defining a relational sudoku puzzle"); 
}

void generateIntSudoku(rel[int, int, int] filledInCells, loc locationToSave) {
  str gridBound = intercalate(",", ["\<n<c>,n<r>,c<c>_<r>\>" | int c <- [1..10], int r <- [1..10]]);
  
  str problem = "{n1,n2,n3,n4,n5,n6,n7,n8,n9,<intercalate(",",[val | int c <- [1..10], int r <- [1..10], str val := ((/<c,r, int v> := filledInCells) ? "c<c>_<r>(int)=<v>" : "c<c>_<r>(int)")])>}
                '
                'num: 1 [{\<n1\>,\<n2\>,\<n3\>,\<n4\>,\<n5\>,\<n6\>,\<n7\>,\<n8\>,\<n9\>},{\<n1\>,\<n2\>,\<n3\>,\<n4\>,\<n5\>,\<n6\>,\<n7\>,\<n8\>,\<n9\>}]
                'cell:1 [{<intercalate(",", ["\<c<c>_<r>\>" | int c <- [1..10], int r <- [1..10]])>},{<intercalate(",", ["\<c<c>_<r>\>" | int c <- [1..10], int r <- [1..10]])>}]
                'r1:  1 [{\<n1\>,\<n2\>,\<n3\>},{\<n1\>,\<n2\>,\<n3\>}]
                'r2:  1 [{\<n4\>,\<n5\>,\<n6\>},{\<n4\>,\<n5\>,\<n6\>}]
                'r3:  1 [{\<n7\>,\<n8\>,\<n9\>},{\<n7\>,\<n8\>,\<n9\>}]
                'grid:3 [{<gridBound>},{<gridBound>}]
                '
                'r1 in num
                'r2 in num
                'r3 in num
                'grid in num-\>num-\>cell
                '
                'forall x: num, y: num | grid[x][y] != grid[x][num\\y]
                ";
  
  writeFile(locationToSave + "sudoku.alle", problem);
  println("done defining the integer sudoku puzzle");
}