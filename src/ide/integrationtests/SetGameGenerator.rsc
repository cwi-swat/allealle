module ide::integrationtests::SetGameGenerator

import List;
import IO;

void generateRelationalSetGame(loc output) {
  str problem = "{<intercalate(",", ["c<i>" | int i <- [1..13]])>,red,green,purple,squiggle,oval,diamond,onee,two,three,open,striped,solid}
              '
              '// Color property
              'Color:1 [{\<red\>,\<green\>,\<purple\>},{\<red\>,\<green\>,\<purple\>}]
              'cardColor:2 [{},{<intercalate(",", ["\<c<i>,red\>,\<c<i>,green\>,\<c<i>,purple\>" | int i <- [1..13]])>}]
              ' 
              '// Symbol property
              'Symbol:1 [{\<squiggle\>,\<oval\>,\<diamond\>},{\<squiggle\>,\<oval\>,\<diamond\>}]
              'cardSymbol:2 [{}, {<intercalate(",", ["\<c<i>,squiggle\>,\<c<i>,oval\>,\<c<i>,diamond\>" | int i <- [1..13]])>}] 
              '
              '// Nr of shapes property
              'NrOfShapes:1 [{\<onee\>,\<two\>,\<three\>},{\<onee\>,\<two\>,\<three\>}]
              'cardNrOfShapes:2 [{}, {<intercalate(",", ["\<c<i>,onee\>,\<c<i>,two\>,\<c<i>,three\>" | int i <- [1..13]])>}]
              '
              '// Shadings property
              'Shading:1 [{\<open\>,\<striped\>,\<solid\>},{\<open\>,\<striped\>,\<solid\>}]
              'cardShading:1 [{},{<intercalate(",", ["\<c<i>,open\>,\<c<i>,striped\>,\<c<i>,solid\>" | int i <- [1..13]])>}]
              '
              'Card:1 [{<intercalate(",", ["\<c<i>\>" | int i <- [1..13]])>},{<intercalate(",", ["\<c<i>\>" | int i <- [1..13]])>}]
              'InSet:1 [{},{<intercalate(",", ["\<c<i>\>" | int i <- [1..13]])>}]
              '
              '// Cards can have only one color, symbol, nr of shapes and shading
              'forall c:Card | one c.cardColor && one c.cardSymbol && one c.cardNrOfShapes && one c.cardShading
              '
              '// Make sure that all the cards on the table are distinct
              'forall c1:Card, c2:Card\\c1 | no (c1.cardColor & c2.cardColor) || no (c1.cardSymbol & c2.cardSymbol) || no (c1.cardNrOfShapes & c2.cardNrOfShapes) || no (c1.cardShading & c2.cardShading) 
              ";
              
  writeFile(output, problem);
}