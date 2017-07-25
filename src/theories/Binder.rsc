module theories::Binder

import logic::Propositional;
import theories::AST;

import List;
import Map;
import Set;
import IO;

alias Index = list[Atom]; 

alias RelationMatrix = map[Index, Formula];
alias AttributeMatrix = map[Index, Formula];

alias RelationAndAttributes = tuple[RelationMatrix relation, AttributeMatrix att];
alias Environment = map[str, RelationAndAttributes]; 

@memo
int sizeOfUniverse(Universe u) = size(u.atoms);

int arity(RelationAndAttributes rm) = 0 when rm.relation == ();
int arity(RelationAndAttributes rm) = size(getOneFrom(rm.relation)) when rm.relation != ();

@memo
private bool sameArity(RelationAndAttributes lhs, RelationAndAttributes rhs) = arity(lhs) == arity(rhs); 

private RelationAndAttributes square(RelationAndAttributes m, int i, int size) = m when i >= size;
private RelationAndAttributes square(RelationAndAttributes m, int i, int size) = or(n, \join(n, n)) when RelationAndAttributes n := square(m, i * 2, size); 

@memo
private list[Index] constructIdentityIndex(int arity, Universe uni) = [vector | AtomDecl ad <- uni.atoms, list[Atom] vector := [ad.atom | int _ <- [0..arity]]];

@memo
RelationAndAttributes identity(RelationAndAttributes orig, Universe uni) = identity(arity(orig), uni);
RelationAndAttributes identity(int arity, Universe uni) {
  RelationMatrix relIden = ();
  
  for (Index idx <- constructIdentityIndex(arity, uni)) {
    relIden[idx] = \true();
  }

  return <relIden,()>;
}

private bool hasSelectedAttributes(RelationAndAttributes raa) = raa.att != ();

RelationAndAttributes or(RelationAndAttributes lhs, RelationAndAttributes rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "OR only works on relations of same arity";
  }
  if (hasSelectedAttributes(lhs) || hasSelectedAttributes(rhs)) {
    throw "OR only works on base relations";
  }
  
  return <(idx : \or(lhsVal, rhsVal) | Index idx <- (lhs.relation + rhs.relation), Formula lhsVal := ((idx in lhs.relation) ? lhs.relation[idx] : \false()), Formula rhsVal := ((idx in rhs.relation) ? rhs.relation[idx] : \false())), ()>;
}

RelationAndAttributes and(RelationAndAttributes lhs, RelationAndAttributes rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "AND only works on relations of same arity";
  }
  if (hasSelectedAttributes(lhs) || hasSelectedAttributes(rhs)) {
    throw "AND only works on base relations";
  }
  
  return <(idx : \and(lhs.relation[idx], rhs.relation[idx]) | Index idx <- lhs.relation, idx in rhs.relation), ()>;
}

RelationAndAttributes transpose(RelationAndAttributes m) {
  if (hasSelectedAttributes(m)) {
    throw "TRANSPOSE only works on base relations";
  }
  
  return <(reverse(idx) : m.relation[idx] | Index idx <- m.relation), ()>;
} 

RelationAndAttributes transitiveClosure(RelationAndAttributes m) {
  if (arity(m) != 2) {
    throw "TRANSITIVE CLOSURE only works on binary relations";
  }
  if (hasSelectedAttributes(m)) {
    throw "TRANSITIVE CLOSURE only works on base relations";
  }
  
  set[Atom] rows = {a | [Atom a, Atom _] <- m.relation}; 

  return square(m, 1, size(rows));
}


RelationAndAttributes reflexiveTransitiveClosure(RelationAndAttributes m, Universe uni) {
  if (arity(m) != 2) {
    throw "REFLEXIVE TRANSITIVE CLOSURE only works on binary relations";
  }
  if (hasSelectedAttributes(m)) {
    throw "REFLEXIVE TRANSITIVE CLOSURE only works on base relations";
  }
  
  return or(transitiveClosure(m), identity(m, uni));
} 

RelationAndAttributes difference(RelationAndAttributes lhs, RelationAndAttributes rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "DIFFERENCE only works on relations of same arity";
  }
  if (hasSelectedAttributes(lhs) || hasSelectedAttributes(rhs)) {
    throw "DIFFERENCE only works on base relations";
  }  
  
  return <(idx : \and(lhs.relation[idx], rhsVal) | Index idx <- lhs.relation, Formula rhsVal := ((idx in rhs.relation) ? not(rhs.relation[idx]) : \true())), ()>;
} 

@memo
RelationAndAttributes \join(RelationAndAttributes lhs, RelationAndAttributes rhs) {
  int arityLhs = arity(lhs);
  int arityRhs = arity(rhs);
    
  if (arityLhs == 1 && arityRhs == 1) { 
    throw "JOIN only works on two non-unary relations"; 
  }
  if (hasSelectedAttributes(lhs) || hasSelectedAttributes(rhs)) {
    throw "JOIN only works on base relations";
  }
        
  set[Index] indicesEndingWith(Atom a, RelationMatrix b) = {idx | Index idx <- b, idx[-1] == a};
  set[Index] indicesStartingWith(Atom a, RelationMatrix b) = {idx | Index idx <- b, idx[0] == a};

  set[Atom] mostRightAtomInLhs = {idx[-1] | Index idx <- lhs.relation};
    
  RelationMatrix relResult = ();
  for (Atom current <- mostRightAtomInLhs) {
    set[Index] lhsIndices = indicesEndingWith(current, lhs.relation);
    set[Index] rhsIndices = indicesStartingWith(current, rhs.relation);
    
    if (lhsIndices != {} && rhsIndices != {}) {  
      for (Index lhsIdx <- lhsIndices, lhs.relation[lhsIdx] != \false(), Index rhsIdx <- rhsIndices, rhs.relation[rhsIdx] != \false()) {
        Formula val = and(lhs.relation[lhsIdx], rhs.relation[rhsIdx]);
        
        Index joinIdx = (lhsIdx - lhsIdx[-1]) + (rhsIdx - rhsIdx[0]);

        if (joinIdx notin relResult) {
          relResult[joinIdx] = val;
        } else {
          relResult[joinIdx] = \or(relResult[joinIdx], val); 
        }
      }
    }
  }
  
  return <relResult, ()>;
}

RelationAndAttributes product(RelationAndAttributes lhs, RelationAndAttributes rhs) {
  if (hasSelectedAttributes(lhs) || hasSelectedAttributes(rhs)) {
    throw "PRODUCT only works on base relations";
  }

  return <(lhsIdx + rhsIdx : \and(lhs.relation[lhsIdx], rhs.relation[rhsIdx]) | Index lhsIdx <- lhs.relation, lhs.relation[lhsIdx] != \false(), Index rhsIdx <- rhs.relation, rhs.relation[rhsIdx] != \false()), ()>;
}

RelationAndAttributes ite(Formula \case, RelationAndAttributes \then, RelationAndAttributes \else) {
  if (arity(then) != arity(\else)) {
    throw "Arity of relation in THEN must be equal to the arity of the relation in ELSE for the ITE to work";
  }
    if (hasSelectedAttributes(\then) || hasSelectedAttributes(\else)) {
    throw "ITE only works on base relations";
  }

  if (\case == \true()) {
    return then;
  } else if (\case == \false()) {
    return \else;
  } 
  
  RelationMatrix relResult = ();
  
  for (Index idx <- (then.relation + \else.relation)) {
    Formula thenRel = ((idx in then.relation) ? then.relation[idx] : \false());
    Formula elseRel = ((idx in \else.relation) ? \else.relation[idx] : \false()); 
    
    relResult[idx] = ite(\case, thenRel, elseRel);
  } 
  
  return <relResult,()>;
}
