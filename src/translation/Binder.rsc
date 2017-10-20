module translation::Binder

import logic::Propositional;
import translation::AST;
import translation::Dimensions;
import List;
import Map;
import Set;
import IO;

import util::Math;

alias Index = int;

data Cell 
  = relOnly(Formula relForm)
  | relAndAtt(Formula relForm, Formula attForm)
  ;

alias RelationMatrix = tuple[Dimensions dim, map[Index, Cell] cells];

alias Environment = tuple[map[str, RelationMatrix] relations, map[list[Id], map[str, Formula]] attributes, list[Id] universe]; 

private bool sameArity(RelationMatrix lhs, RelationMatrix rhs) = lhs.dim.arity == rhs.dim.arity;  

@memo
int getIntIndex(list[Id] atomVector, list[Id] atomsInUniverse) {
  int multiplier = 1;
  int index = 0;
  int uniSize = size(atomsInUniverse);
  
  for (int i <- [size(atomVector)-1..-1]) {
    index += indexOf(atomsInUniverse, atomVector[i]) * multiplier;
    multiplier *= uniSize;
  }
  
  return index;
}

@memo
list[Id] getVectorIndex(int index, int arity, list[Id] atomsInUniverse) {
  list[Id] vector = [];
  int multiplier = 1;
  int uniSize = size(atomsInUniverse);
  
  for (int i <- [0..arity]) {
    vector = atomsInUniverse[(index / multiplier) % uniSize] + vector;
    multiplier *= uniSize;
  }
  
  return vector;
}

@memo
RelationMatrix universe(int universeSize) = <square(1,universeSize), (i : relOnly(\true()) | int i <- [0..universeSize])>;

@memo
RelationMatrix identity(int universeSize) = <square(2,universeSize), (i*universeSize + i : relOnly(\true()) | int i <- [0..universeSize])>;

RelationMatrix or(RelationMatrix lhs, RelationMatrix rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "OR only works on relations of same arity";
  }
  
  return <lhs.dim, (idx : relOnly(\or(lhsVal, rhsVal)) | Index idx <- (lhs.cells + rhs.cells), Formula lhsVal := ((idx in lhs.cells) ? lhs.cells[idx].relForm : \false()), Formula rhsVal := ((idx in rhs.cells) ? rhs.cells[idx].relForm : \false()))>;
}

RelationMatrix and(RelationMatrix lhs, RelationMatrix rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "AND only works on relations of same arity";
  }
  
  return <lhs.dim, (idx : relOnly(\and(lhs.cells[idx].relForm, rhs.cells[idx].relForm)) | Index idx <- lhs.cells, idx in rhs.cells)>;
}

RelationMatrix transpose(RelationMatrix m) {
  if (m.dim.arity != 2) {
    throw "TRANSPOSE only works on binary relations";
  }
  
  int rows = m.dim.size;
  int cols = m.dim.size;
      
  return <m.dim, ((idx%cols)*rows + (idx / cols) : m.cells[idx] | Index idx <- m.cells)>;
} 

RelationMatrix transitiveClosure(RelationMatrix m) {
  if (m.dim.arity != 2) {
    throw "TRANSITIVE CLOSURE only works on binary relations";
  }
  
  int rows = 0;
  int lastRow = -1;
  for (Index idx <- m.cells, idx / m.dim.size > lastRow) {
    rows += 1;
    lastRow = idx / m.dim.size;
  } 

  int i = 1;
  RelationMatrix ret = m;
  while (i < rows) {
    ret = or(ret, dotJoin(ret,ret));
    i*=2;
  }
  
  return ret;
}

RelationMatrix reflexiveTransitiveClosure(RelationMatrix m, Environment env) {
  if (m.dim.arity != 2) {
    throw "REFLEXIVE TRANSITIVE CLOSURE only works on binary relations";
  }
  
  return or(transitiveClosure(m), identity(m.dim.size));
} 

RelationMatrix difference(RelationMatrix lhs, RelationMatrix rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "DIFFERENCE only works on relations of same arity";
  }
  
  return <lhs.dim, (idx : relOnly(\and(lhs.cells[idx].relForm, rhsVal)) | Index idx <- lhs.cells, Formula rhsVal := ((idx in rhs.cells) ? not(rhs.cells[idx].relForm) : \true()))>;
}  

RelationMatrix dotJoin(RelationMatrix lhs, RelationMatrix rhs) {
  if (lhs.dim.arity == 1 && rhs.dim.arity == 1) { 
    throw "JOIN only works on two non-unary relations"; 
  }
  
  if (lhs.cells == () || rhs.cells == ()) {
    return <dotJoin(lhs.dim, rhs.dim), ()>;
  }  
        
  map[Index,Cell] rCells = ();
  int b = rhs.dim.size;
  int c = capacity(rhs.dim) / b;
  
  for (Index lIdx <- lhs.cells) {
    int rowHead = (lIdx % b)*c;
    int rowTail = rowHead + c - 1;
    
    for (Index rIdx <- rhs.cells, rIdx >= rowHead, rIdx <= rowTail) {
      Formula val = and(lhs.cells[lIdx].relForm, rhs.cells[rIdx].relForm);
      if (val != \false()) {
        int k = (lIdx / b)*c + rIdx%c;
        if (val == \true()) { 
          rCells[k] = relOnly(\true());
        } else if (k in rCells) {
          rCells[k] = relOnly(\or(val, rCells[k].relForm));
        } else {
          rCells[k] = relOnly(val);
        }
      }
    }
  }
   
  return <dotJoin(lhs.dim, rhs.dim), rCells>; 
}

RelationMatrix product(RelationMatrix lhs, RelationMatrix rhs) {
  int rCap = capacity(rhs.dim);
  RelationMatrix productResult = <cross(lhs.dim, rhs.dim), (rCap * lIdx + rIdx : relOnly(\and(lhs.cells[lIdx].relForm, rhs.cells[rIdx].relForm)) | Index lIdx <- lhs.cells, lhs.cells[lIdx].relForm != \false(), Index rIdx <- rhs.cells, rhs.cells[rIdx].relForm != \false())>;
  
  return productResult;
}

RelationMatrix ite(Formula \case, RelationMatrix \then, RelationMatrix \else) {
  if (!sameArity(then,\else)) {
    throw "Arity of relation in THEN must be equal to the arity of the relation in ELSE for the ITE to work";
  }

  if (\case == \true()) {
    return then;
  } else if (\case == \false()) {
    return \else;
  } 
  
  map[Index,Cell] rCells = ();
  
  for (Index idx <- (then.cells + \else.cells)) {
    Formula thenRel = ((idx in then.cells) ? then.cells[idx].relForm : \false());
    Formula elseRel = ((idx in \else.cells) ? \else.cells[idx].relForm : \false()); 
    
    rCells[idx] = relOnly(ite(\case, thenRel, elseRel));
  } 
  
  return <then.dim, rCells>;
}
