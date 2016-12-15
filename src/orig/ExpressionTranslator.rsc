module orig::ExpressionTranslator

import logic::Propositional;
import orig::AST;

import List;
import Relation;
import Map;
import Set;
import IO;

// index is a tuple of different arity depending on type of relation (unary, binary) 
alias Index = list[Atom];
alias Binding = map[Index, Formula]; 

@memo
private int sizeOfUniverse(Universe u) = size(u.atoms); 

private int arity(Binding b) {
  for (Index idx <- b) {
    return size(idx);
  }
}

private bool sameArity(Binding lhs, Binding rhs) = arity(lhs) == arity(rhs); 

private Binding square(Binding m, int i, int sizeOfUniverse) = m when i >= sizeOfUniverse;
private Binding square(Binding m, int i, int sizeOfUniverse) = or(n, \join(n, n)) when Binding n := square(m, i * 2, sizeOfUniverse); 

private list[Index] constructIdentityIndex(int arity, Universe uni) = [idx | Atom a <- uni.atoms, Index idx := [a | int _ <- [0..arity]]];

@memo
private Binding identity(Binding orig, Universe uni) = identity(arity(orig), uni);
private Binding identity(int arity, Universe uni) = (idx:\true() | Index idx <- constructIdentityIndex(arity, uni));

private Binding or(Binding lhs, Binding rhs) = (x:\or(lhsVal,rhsVal) | Index x <- (lhs + rhs), Formula lhsVal := ((x in lhs) ? lhs[x] : \false()), Formula rhsVal := ((x in rhs) ? rhs[x] : \false())) when sameArity(lhs, rhs);
private default Binding or(Binding _, Binding _) { throw "Unable to perform disjunction of bindings with different arity"; }

private Binding and(Binding lhs, Binding rhs) = (x:\and(lhs[x],rhs[x]) | Index x <- lhs, x in rhs) when sameArity(lhs, rhs);
private default Binding and(Binding _, Binding _) { throw "Unable to perform conjunction of bindings with different arity"; }

Binding transpose(Binding m, Universe uni) = (() | it + (reverse(key) : m[key]) | Index key <- m);

Binding transitiveClosure(Binding m, Universe uni) = square(m, 1, sizeOfUniverse(uni)) when arity(m) == 2;
default Binding transitiveClosure(Binding m, Universe uni) { throw "Can not perform a transitive closure on a non-binary relation"; }

Binding reflexiveTransitiveClosure(Binding m, Universe uni) = or(transitiveClosure(m, uni), identity(m, uni)) when arity(m) == 2; 
default Binding reflexiveTransitiveClosure(Binding m, Universe uni) { throw "Can not perform a reflexive transitive closure on a non-binary relation"; }

Binding disjunction(Binding lhs, Binding rhs) = or(lhs, rhs) when sameArity(lhs, rhs);
default Binding disjunction(Binding lhs, Binding rhs) { throw "Can not perform a disjunction on two relations with different arities"; }  

Binding conjunction(Binding lhs, Binding rhs) = and(lhs, rhs) when sameArity(lhs, rhs);
default Binding conjunction(Binding lhs, Binding rhs) { throw "Can not perform a conjunction on two relations with different arities"; }

Binding difference(Binding lhs, Binding rhs) = (idx:and(lhs[idx], rhsVal) |Index idx <- lhs, Formula rhsVal := ((idx in rhs) ? not(rhs[idx]) : \true())) when sameArity(lhs, rhs);
default Binding different(Binding lhs, Binding rhs) { throw "Can not perform a difference on two relations with different arities"; }  

@memo private set[Index] indicesEndingWith(Atom a, Binding b, int arity) = {idx | Index idx <- b, idx[arity - 1] == a};
@memo private set[Index] indicesStartingWith(Atom a, Binding b) = {idx | Index idx <- b, idx[0] == a};

Binding \join(Binding lhs, Binding rhs) {
  if (arity(lhs) == 1 && arity(rhs) == 1) { throw "Unable to join two unary relations"; }
  int arityLhs = arity(lhs);

  // join by joining the right-most atom from the index of the lhs with the left-most atom from the index of the rhs. It is much like a database join
  //set[Atom] mostRightAtomInLhs = {idx[arityLhs - 1] | Index idx <- lhs};
  
  Binding joinResult = ();
  
  map[Atom, set[Index]] lhsIndicesSortedByLastAtom = ();
  for (Index idx <- lhs) {
    Atom a = idx[arityLhs - 1];
    if (a in lhsIndicesSortedByLastAtom) lhsIndicesSortedByLastAtom[a] += idx;
    else lhsIndicesSortedByLastAtom[a] = {idx};
  } 
  map[Atom, set[Index]] rhsIndicesSortedByFirstAtom = ();
  for (Index idx <- rhs) {
    Atom a = idx[0];
    if (a in rhsIndicesSortedByFirstAtom) rhsIndicesSortedByFirstAtom[a] += idx;
    else rhsIndicesSortedByFirstAtom[a] = {idx};
  }
  
  for (Atom current <- lhsIndicesSortedByLastAtom, current in rhsIndicesSortedByFirstAtom) {
    
    for (Index currentLhs <- lhsIndicesSortedByLastAtom[current], Formula lhsVal := lhs[currentLhs], lhsVal != \false(), Index currentRhs <- rhsIndicesSortedByFirstAtom[current], Formula rhsVal := rhs[currentRhs], rhsVal != \false()) {
      Formula val = and(lhsVal, rhsVal);
        
      if (val != \false()) {
        Index jointIndex = (currentLhs - currentLhs[arityLhs - 1]) + (currentRhs - currentRhs[0]);

        if (jointIndex notin joinResult) { 
          joinResult[jointIndex] = val;
        } else {
          joinResult[jointIndex] = or(joinResult[jointIndex], val);
        }
      }
    }
  }
  
  return joinResult;
}
	
Binding product(Binding lhs, Binding rhs) = (currentLhs + currentRhs : val | Index currentLhs <- lhs<0>, Index currentRhs <- rhs<0>, Formula val := and(lhs[currentLhs], rhs[currentRhs]), val !:= \false()); 

