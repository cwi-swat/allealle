module theories::Binder

import logic::Propositional;
import theories::AST;

import List;
import Map;
import Set;
import IO;

alias Index = list[Atom]; 

alias RelationMatrix = map[Index, Formula];

data AttributeFormula = implies(Formula relForm, Formula attributeForm); 
alias Attributes = map[str, set[AttributeFormula]];
alias AttributeMatrix = map[Index, map[int, Attributes]];

alias RelationAndAttributes = tuple[RelationMatrix relation, AttributeMatrix att];
alias Environment = map[str, RelationAndAttributes]; 

@memo
int sizeOfUniverse(Universe u) = size(u.atoms);

int arity(RelationAndAttributes rm) = 0 when rm.relation == ();
int arity(RelationAndAttributes rm) = size(getOneFrom(rm.relation)) when rm.relatin != ();

@memo
private bool sameArity(RelationAndAttributes lhs, RelationAndAttributes rhs) = arity(lhs) == arity(rhs); 

private RelationAndAttributes square(RelationAndAttributes m, int i, int sizeOfUniverse) = m when i >= sizeOfUniverse;
private RelationAndAttributes square(RelationAndAttributes m, int i, int sizeOfUniverse) = or(n, \join(n, n)) when RelationAndAttributes n := square(m, i * 2, sizeOfUniverse); 

private list[Index] constructIdentityIndex(int arity, Universe uni) = [vector | AtomDecl ad <- uni.atoms, list[Atom] vector := [ad.atom | int _ <- [0..arity]]];

@memo
RelationAndAttributes identity(RelationAndAttributes orig, Universe uni) = identity(arity(orig), uni);
RelationAndAttributes identity(int arity, Universe uni) = (idx:<\true(),()> | Index idx <- constructIdentityIndex(arity, uni));

map[int, Attributes] merge(map[int, Attributes] lhs, map[int, Attributes] rhs) = (idx : lhs[idx] | int idx <- lhs, idx notin rhs) +
                                                                                 (idx : lhs[idx] + rhs[idx] | int idx <- lhs, idx in rhs) +
                                                                                 (idx : rhs[idx] | int idx <- rhs, idx notin lhs);

RelationAndAttributes or(RelationAndAttributes lhs, RelationAndAttributes rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "Unable to perform disjunction of relations with different arity";
  }
  
  RelationMatrix relResult = ();
  AttributeMatrix attResult = ();
  
  for (Index idx <- (lhs.relation + rhs.relation)) {
    Formula lhsVal = idx in lhs.relation ? lhs.relation[idx] : \false();
    Formula rhsVal = idx in rhs.relation ? rhs.rleation[idx] : \false();
    relResult[idx] = \or(lhsVal, rhsVal);
    
    map[int, Attributes] lhsAtt = idx in lhs.att ? lhs.att[idx] : ();
    map[int, Attributes] rhsAtt = idx in rhs.att ? rhs.att[idx] : ();
    attResult[idx] = merge(lhsAtt, rhsAtt);    
  }
  
  return <relResult, attResult>;
}

RelationAndAttributes and(RelationAndAttributes lhs, RelationAndAttributes rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "Unable to perform conjunction of relations with different arity";
  }

  RelationMatrix relResult = ();
  AttributeMatrix attResult = ();
  
  for (Index idx <- lhs.relation, idx in rhs.relation) {
    relResult[idx] = \and(lhs.relation[idx], rhs.relation[idx]);
    attResult[idx] = merge(lhs.attResult[idx], lhs.attResult[idx]);    
  }
  
  return <relResult, attResult>;
}

RelationAndAttributes transpose(RelationAndAttributes m) {
  int arity = arity(m);
  
  RelationMatrix relResult = ();
  AttributeMatrix attResult = ();
  
  for (Index idx <- m.relation) {
    Index reversedIdx = reverse(idx);
    
    relResult[reversedIdx] = m.relation[idx];
    attResult[reversedIdx] = ((arity - 1) - i : m.att[idx][i] | int i <- m.att[idx]);  
  }

  return <relResult, attResult>;
} 

RelationAndAttributes transitiveClosure(RelationAndAttributes m, Universe uni) {
  if (artiy(m) != 2) {
    throw "Can not perform a transitive closure on a non-binary relation";
  }
  
  return square(m, 1, sizeOfUniverse(uni));
}


RelationAndAttributes reflexiveTransitiveClosure(RelationAndAttributes m, Universe uni) {
  if (artiy(m) != 2) {
    throw "Can not perform a reflexive transitive closure on a non-binary relation";
  }
  
  return or(transitiveClosure(m, uni), identity(m, uni));
} 

RelationAndAttributes difference(RelationAndAttributes lhs, RelationAndAttributes rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "Can not perform a difference on two relations with different arities";
  }
  
  RelationMatrix relResult = ();
  AttributeMatrix attResult = ();
  
  for (Index idx <- lhs) {
    Formula rhsVal = idx in rhs.relation ? not(rhs.relation[idx]) : \true();
    
    relResult[idx] = \and(lhs.relation[idx], rhsVal);
    attResult[idx] = lhs.att[idx];
  }
  
  return <relResult, attResult>;
} 

RelationAndAttributes \join(RelationAndAttributes lhs, RelationAndAttributes rhs) {
  int arityLhs = arity(lhs);
  int arityRhs = arity(rhs);
    
  if (arityLhs == 1 && arityRhs == 1) { 
    throw "Unable to join two unary relations"; 
  }
      
  set[Index] indicesEndingWith(Atom a, RelationMatrix b) = {idx | Index idx <- b, idx[-1] == a};
  set[Index] indicesStartingWith(Atom a, RelationMatrix b) = {idx | Index idx <- b, idx[0] == a};

  set[Atom] mostRightAtomInLhs = {idx[-1] | Index idx <- lhs.relation};
    
  RelationMatrix relResult = ();
  AttributeMatrix attResult = ();
  
  for (Atom current <- mostRightAtomInLhs) {
    set[Index] lhsIndices = indicesEndingWith(current, lhs);
    set[Index] rhsIndices = indicesStartingWith(current, rhs);
    
    if (lhsIndices != {} && rhsIndices != {}) {  
      for (Index lhsIdx <- lhsIndices, lhs.relation[lhsIdx] != \false(), Index rhsIdx <- rhsIndices, rhs.relation[rhsIdx] != \false()) {
        Formula val = and(lhs.relation[lhsIdx], rhs.relation[rhsIdx]);
        
        Index joinIdx = (lhsIdx - lhsIdx[-1]) + (rhsIdx - rhsIdx[0]);
        map[int, Attributes] attJoin = (lhs.att[lhsIdx] - lhs.att[lhsIdx][arityLhs-1]) + (rhs.att[rhsIdx] - rhs.att[rhsIdx][0]);

        if (joinIdx notin relResult) {
          relResult[joinIdx] = val;
          attResult[joinIdx] = attJoin;
        } else {
          relResult[joinIdx] = \or(relResult[joinIdx], val); 
          attResult[joinIdx] = merge(attResult[joinIdx], attJoin);
        }
      }
    }
  }
  
  return <relResult, attResult>;
}

RelationAndAttributes product(RelationAndAttributes lhs, RelationAndAttributes rhs) {
  RelationMatrix relResult = ();
  AttributeMatrix attResult = ();
  int arityLhs = arity(lhs);
  
  for (Indx lhsIdx <- lhs.relation, lhs.relation[lhsIdx] != \false(), Index rhsIdx <- rhs.relation, rhs.relation[rhsIdx] != \false()) {
    Index productIdx = lhsIdx + rhsIdx;
   
    relResult[productIdx] = \and(lhs.relation[lhsIdx], rhs.relation[rhsIdx]);
    attResult[productIdx] = lhs.att[lhsIdx] + (i + arityLhs : rhs.att[rhsIdx][i] | int i <- rhs.att[rhsIdx]); 
  }
  
  return <relResult, attResult>;
}
