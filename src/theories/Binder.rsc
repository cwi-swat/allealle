module theories::Binder

import logic::Propositional;
import theories::AST;

import List;
import Map;
import Set;
import IO;

alias Index = list[Atom]; 

alias RelationMatrix = map[Index, Formula];
 
alias AttributeFormula = tuple[Formula relForm, Formula attForm]; 
alias Attributes = map[str, set[AttributeFormula]];
alias AttributeMatrix = map[Index, map[int, Attributes]];

alias RelationAndAttributes = tuple[RelationMatrix relation, AttributeMatrix att];
alias Environment = map[str, RelationAndAttributes]; 

data Command;

@memo
int sizeOfUniverse(Universe u) = size(u.atoms);

int arity(RelationAndAttributes rm) = 0 when rm.relation == ();
int arity(RelationAndAttributes rm) = size(getOneFrom(rm.relation)) when rm.relation != ();

@memo
private bool sameArity(RelationAndAttributes lhs, RelationAndAttributes rhs) = arity(lhs) == arity(rhs); 

private RelationAndAttributes square(RelationAndAttributes m, int i, int sizeOfUniverse) = m when i >= sizeOfUniverse;
private RelationAndAttributes square(RelationAndAttributes m, int i, int sizeOfUniverse) = or(n, \join(n, n)) when RelationAndAttributes n := square(m, i * 2, sizeOfUniverse); 

private list[Index] constructIdentityIndex(int arity, Universe uni) = [vector | AtomDecl ad <- uni.atoms, list[Atom] vector := [ad.atom | int _ <- [0..arity]]];

@memo
RelationAndAttributes identity(RelationAndAttributes orig, Universe uni) = identity(arity(orig), uni);
RelationAndAttributes identity(int arity, Universe uni) {
  RelationMatrix relIden = ();
  AttributeMatrix attIden = ();
  
  for (Index idx <- constructIdentityIndex(arity, uni)) {
    relIden[idx] = \true();
    attIden[idx] = ();
  }

  return <relIden,attIden>;
}
  
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
    Formula rhsVal = idx in rhs.relation ? rhs.relation[idx] : \false();
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
    attResult[idx] = merge(lhs.att[idx], rhs.att[idx]);    
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
  if (arity(m) != 2) {
    throw "Can not perform a transitive closure on a non-binary relation";
  }
  
  return square(m, 1, sizeOfUniverse(uni));
}


RelationAndAttributes reflexiveTransitiveClosure(RelationAndAttributes m, Universe uni) {
  if (arity(m) != 2) {
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
  
  for (Index idx <- lhs.relation) {
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
  
  map[int, Attributes] attributeJoin(map[int, Attributes] lhsAtt, map[int, Attributes] rhsAtt) = (i  :lhsAtt[i] | int i <- lhsAtt, i < (arityLhs - 1)) +
                                                                                                 (i-1:rhsAtt[i] | int i <- rhsAtt, i > 0);
  
  for (Atom current <- mostRightAtomInLhs) {
    set[Index] lhsIndices = indicesEndingWith(current, lhs.relation);
    set[Index] rhsIndices = indicesStartingWith(current, rhs.relation);
    
    if (lhsIndices != {} && rhsIndices != {}) {  
      for (Index lhsIdx <- lhsIndices, lhs.relation[lhsIdx] != \false(), Index rhsIdx <- rhsIndices, rhs.relation[rhsIdx] != \false()) {
        Formula val = and(lhs.relation[lhsIdx], rhs.relation[rhsIdx]);
        
        Index joinIdx = (lhsIdx - lhsIdx[-1]) + (rhsIdx - rhsIdx[0]);
        map[int, Attributes] attJoin = attributeJoin(lhs.att[lhsIdx], rhs.att[rhsIdx]);

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
  
  for (Index lhsIdx <- lhs.relation, lhs.relation[lhsIdx] != \false(), Index rhsIdx <- rhs.relation, rhs.relation[rhsIdx] != \false()) {
    Index productIdx = lhsIdx + rhsIdx;
   
    relResult[productIdx] = \and(lhs.relation[lhsIdx], rhs.relation[rhsIdx]);
    attResult[productIdx] = lhs.att[lhsIdx] + (i + arityLhs : rhs.att[rhsIdx][i] | int i <- rhs.att[rhsIdx]); 
  }
  
  return <relResult, attResult>;
}
