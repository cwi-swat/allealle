module translation::tests::binderTests::TesterBase

import translation::Binder;
import translation::Dimensions;
import logic::Propositional;

import Map;
import List;
import IO;
 
alias SimpleRelationMatrix = map[list[str], Cell];

str toVarName(list[str] vector, str relName) = "<relName>_<intercalate("_", vector)>";

SimpleRelationMatrix truth(list[str] vector) = (vector : relOnly(\true()));
SimpleRelationMatrix truths(list[list[str]] vectors) = (() | it + truth(v) | list[str] v <- vectors);

SimpleRelationMatrix var(list[str] vector, str relName) = (vector : relOnly(var(toVarName(vector, relName)))); 
SimpleRelationMatrix var(list[str] vector, Formula f) = (vector : relOnly(f)); 
SimpleRelationMatrix vars(list[list[str]] vectors, str relName) = (() | it + var(v, relName) | list[str] v <- vectors);

SimpleRelationMatrix compose(list[SimpleRelationMatrix] matrices) = (() | it + m | m <- matrices);

list[str] constructUniverse(list[SimpleRelationMatrix] matrices) = dup([a | SimpleRelationMatrix m <- matrices, list[str] vector <- m, str a <- vector]); 

int arity(SimpleRelationMatrix sm) = size(getOneFrom(sm));

int getIntIndex(list[str] atomVector, list[str] atomsInUniverse) {
  int multiplier = 1;
  int index = 0;
  
  for (int i <- [size(atomVector)-1..-1]) {
    index += indexOf(atomsInUniverse, atomVector[i]) * multiplier;
    multiplier *= size(atomsInUniverse);
  }
  
  return index;
}

list[str] getVectorIndex(int index, int arity, list[str] atomsInUniverse) {
  list[str] vector = [];
  int multiplier = 1;
  
  for (int i <- [0..arity]) {
    vector = atomsInUniverse[(index / multiplier) % size(atomsInUniverse)] + vector;
    multiplier *= size(atomsInUniverse);
  }
  
  return vector;
}

RelationMatrix convert(SimpleRelationMatrix sm, list[str] atomsInUniverse) = <square(arity(sm), size(atomsInUniverse)), (getIntIndex(idx, atomsInUniverse) : sm[idx] | list[str] idx <- sm)>; 
SimpleRelationMatrix convert(RelationMatrix m, list[str] atomsInUniverse) = (getVectorIndex(idx, m.dim.arity, atomsInUniverse) : m.cells[idx] | int idx <- m.cells);

test bool conversionTest() {
  pigeon = truths([["p1"],["p2"]]);
  hole = truths([["h1"],["h2"]]);
  nest = vars([["p1","h1"],["p1","h2"],["p2","h1"],["p2","h2"]], "nest");
  
  list[str] uni = constructUniverse([pigeon,hole,nest]);
  
  return pigeon == convert(convert(pigeon, uni), uni) &&
         hole == convert(convert(hole, uni), uni) &&
         nest == convert(convert(nest, uni), uni);
}

test bool conversionTest2() {
  a = truths([["a","a","a"],["a","b","c"],["b","a","b"]]);
  
  list[str] uni = constructUniverse([a]);
  
  return a == convert(convert(a, uni), uni);
}
