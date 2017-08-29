module ide::integrationtests::NQueensGenerator

import IO;
import List;

void generateNQueensIntProblem(int n) {
  str problem = "{<intercalate(",", ["q<i>{x(int),y(int)}" | int i <- [1..n+1]])>}
                '
                'Queen:1 [{<intercalate(",", ["\<q<i>\>" | int i <- [1..n+1]])>},{<intercalate(",", ["\<q<i>\>" | int i <- [1..n+1]])>}]
                '
                'Queen::x \>= 1 && Queen::x \<=<n>
                'Queen::y \>= 1 && Queen::y \<=<n>
                '
                '// Queens cannot be on the same row or column or on the diagonal
                'forall q:Queen, q\':Queen\\q | q::x != q\'::x && q::y != q\'::y && |q::x - q\'::x| != |q::y - q\'::y|
                '";

  writeFile(|project://allealle/examples/int/nqueens.alle|, problem);  
}
