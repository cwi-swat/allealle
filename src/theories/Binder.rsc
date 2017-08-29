module theories::Binder

import logic::Propositional;
import theories::AST;

import List;
import Map;
import Set;
import IO;

alias Index = list[Atom]; 

data Cell 
  = relOnly(Formula relForm)
  | relAndAtt(Formula relForm, Formula attForm)
  ;

alias RelationMatrix = map[Index, Cell];

alias Environment = tuple[map[str, RelationMatrix] relations, map[Atom, map[str, Formula]] attributes]; 

int sizeOfUniverse(Universe u) = size(u.atoms);

int arity(RelationMatrix rm) = 0 when rm == ();
default int arity(RelationMatrix rm) = size(getOneFrom(rm));

private bool sameArity(RelationMatrix lhs, RelationMatrix rhs) = arity(lhs) == arity(rhs); 

private RelationMatrix square(RelationMatrix m, int i, int size) = m when i >= size;
private RelationMatrix square(RelationMatrix m, int i, int size) = or(n, \join(n, n)) when RelationMatrix n := square(m, i * 2, size); 

@memo
RelationMatrix identity(Universe uni) = ([ad.atom,ad.atom] : relOnly(\true()) | AtomDecl ad <- uni.atoms);

@memo
RelationMatrix or(RelationMatrix lhs, RelationMatrix rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "OR only works on relations of same arity";
  }
  
  return (idx : relOnly(\or(lhsVal, rhsVal)) | Index idx <- (lhs + rhs), Formula lhsVal := ((idx in lhs) ? lhs[idx].relForm : \false()), Formula rhsVal := ((idx in rhs) ? rhs[idx].relForm : \false()));
}

@memo
RelationMatrix and(RelationMatrix lhs, RelationMatrix rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "AND only works on relations of same arity";
  }
  
  return (idx : relOnly(\and(lhs[idx].relForm, rhs[idx].relForm)) | Index idx <- lhs, idx in rhs);
}

@memo
RelationMatrix transpose(RelationMatrix m) {
  if (arity(m) != 2) {
    throw "TRANSPOSE only works on binary relations";
  }
  
  return (reverse(idx) : m[idx] | Index idx <- m);
} 

@memo
RelationMatrix transitiveClosure(RelationMatrix m) {
  if (arity(m) != 2) {
    throw "TRANSITIVE CLOSURE only works on binary relations";
  }
  
  set[Atom] rows = {a | [Atom a, Atom _] <- m}; 

  return square(m, 1, size(rows));
}

@memo
RelationMatrix reflexiveTransitiveClosure(RelationMatrix m, Universe uni) {
  if (arity(m) != 2) {
    throw "REFLEXIVE TRANSITIVE CLOSURE only works on binary relations";
  }
  
  return or(transitiveClosure(m), identity(uni));
} 

@memo
RelationMatrix difference(RelationMatrix lhs, RelationMatrix rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "DIFFERENCE only works on relations of same arity";
  }
  
  return (idx : relOnly(\and(lhs[idx].relForm, rhsVal)) | Index idx <- lhs, Formula rhsVal := ((idx in rhs) ? not(rhs[idx].relForm) : \true()));
} 

@memo
RelationMatrix \join(RelationMatrix lhs, RelationMatrix rhs) {
  int arityLhs = arity(lhs);
  int arityRhs = arity(rhs);
    
  if (arityLhs == 1 && arityRhs == 1) { 
    throw "JOIN only works on two non-unary relations"; 
  }
        
  set[Index] indicesEndingWith(Atom a, RelationMatrix b) = {idx | Index idx <- b, idx[-1] == a};
  set[Index] indicesStartingWith(Atom a, RelationMatrix b) = {idx | Index idx <- b, idx[0] == a};

  set[Atom] mostRightAtomInLhs = {idx[-1] | Index idx <- lhs};
    
  RelationMatrix relResult = ();
  for (Atom current <- mostRightAtomInLhs) {
    set[Index] lhsIndices = indicesEndingWith(current, lhs);
    set[Index] rhsIndices = indicesStartingWith(current, rhs);
    
    if (lhsIndices != {} && rhsIndices != {}) {  
      for (Index lhsIdx <- lhsIndices, lhs[lhsIdx].relForm != \false(), Index rhsIdx <- rhsIndices, rhs[rhsIdx].relForm != \false()) {
        Formula val = and(lhs[lhsIdx].relForm, rhs[rhsIdx].relForm);
        
        Index joinIdx = (lhsIdx - lhsIdx[-1]) + (rhsIdx - rhsIdx[0]);

        if (joinIdx notin relResult) {
          relResult[joinIdx] = relOnly(val);
        } else {
          relResult[joinIdx] = relOnly(\or(relResult[joinIdx].relForm, val)); 
        }
      }
    }
  }
  
  return relResult;
}

@memo
RelationMatrix product(RelationMatrix lhs, RelationMatrix rhs) {
  return (lhsIdx + rhsIdx : relOnly(\and(lhs[lhsIdx].relForm, rhs[rhsIdx].relForm)) | Index lhsIdx <- lhs, lhs[lhsIdx].relForm != \false(), Index rhsIdx <- rhs, rhs[rhsIdx].relForm != \false());
}

@memo
RelationMatrix ite(Formula \case, RelationMatrix \then, RelationMatrix \else) {
  if (arity(then) != arity(\else)) {
    throw "Arity of relation in THEN must be equal to the arity of the relation in ELSE for the ITE to work";
  }

  if (\case == \true()) {
    return then;
  } else if (\case == \false()) {
    return \else;
  } 
  
  RelationMatrix relResult = ();
  
  for (Index idx <- (then + \else)) {
    Formula thenRel = ((idx in then) ? then[idx].relForm : \false());
    Formula elseRel = ((idx in \else) ? \else[idx].relForm : \false()); 
    
    relResult[idx] = relOnly(ite(\case, thenRel, elseRel));
  } 
  
  return relResult;
}
