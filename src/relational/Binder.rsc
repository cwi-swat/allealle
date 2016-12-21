module relational::Binder

extend Binder;

import logic::Propositional;
import relational::AST;

import List;
//import Relation;
import Map;
import Set;
import IO;

private Binding square(Binding m, int i, int sizeOfUniverse) = m when i >= sizeOfUniverse;
private Binding square(Binding m, int i, int sizeOfUniverse) = or(n, \join(n, n)) when Binding n := square(m, i * 2, sizeOfUniverse); 

private list[Index] constructIdentityIndex(int arity, Universe uni) = [idx | Atom a <- uni.atoms, list[Atom] vector := [a | int _ <- [0..arity]], Index idx := <relational(), vector>];

@memo
private Binding identity(Binding orig, Universe uni) = identity(arity(orig), uni);
private Binding identity(int arity, Universe uni) = (idx:\true() | Index idx <- constructIdentityIndex(arity, uni));

private Binding or(Binding lhs, Binding rhs) = (x:\or(lhsVal,rhsVal) | Index x <- (lhs + rhs), x.theory == relational(), Formula lhsVal := ((x in lhs) ? lhs[x] : \false()), Formula rhsVal := ((x in rhs) ? rhs[x] : \false())) when sameArity(lhs, rhs);
private default Binding or(Binding _, Binding _) { throw "Unable to perform disjunction of bindings with different arity"; }

private Binding and(Binding lhs, Binding rhs) = (x:\and(lhs[x],rhs[x]) | Index x <- lhs, x.theory == relational() , x in rhs) when sameArity(lhs, rhs);
private default Binding and(Binding _, Binding _) { throw "Unable to perform conjunction of bindings with different arity"; }

Binding transpose(Binding m, Universe uni) = (() | it + (reversedIndex : m[key]) | Index key <- m, key.theory == relational(), Index reversedIndex := <relational(), reverse(key.vector)>);

Binding transitiveClosure(Binding m, Universe uni) = square(m, 1, sizeOfUniverse(uni)) when arity(m) == 2;
default Binding transitiveClosure(Binding m, Universe uni) { throw "Can not perform a transitive closure on a non-binary relation"; }

Binding reflexiveTransitiveClosure(Binding m, Universe uni) = or(transitiveClosure(m, uni), identity(m, uni)) when arity(m) == 2; 
default Binding reflexiveTransitiveClosure(Binding m, Universe uni) { throw "Can not perform a reflexive transitive closure on a non-binary relation"; }

Binding disjunction(Binding lhs, Binding rhs) = or(lhs, rhs) when sameArity(lhs, rhs);
default Binding disjunction(Binding lhs, Binding rhs) { throw "Can not perform a disjunction on two relations with different arities"; }  

Binding conjunction(Binding lhs, Binding rhs) = and(lhs, rhs) when sameArity(lhs, rhs);
default Binding conjunction(Binding lhs, Binding rhs) { throw "Can not perform a conjunction on two relations with different arities"; }

Binding difference(Binding lhs, Binding rhs) = (idx:and(lhs[idx], rhsVal) |Index idx <- lhs, idx.theory == relational(), Formula rhsVal := ((idx in rhs) ? not(rhs[idx]) : \true())) when sameArity(lhs, rhs);
default Binding different(Binding lhs, Binding rhs) { throw "Can not perform a difference on two relations with different arities"; }  

@memo private set[Index] indicesEndingWith(Atom a, Binding b, int arity) = {idx | Index idx <- b, idx.theory == relational(), idx.vector[arity - 1] == a};
@memo private set[Index] indicesStartingWith(Atom a, Binding b) = {idx | Index idx <- b, idx.theory == relational(), idx.vector[0] == a};

Binding \join(Binding lhs, Binding rhs) {
  if (arity(lhs) == 1 && arity(rhs) == 1) { throw "Unable to join two unary relations"; }
  int arityLhs = arity(lhs);

  // join by joining the right-most atom from the index of the lhs with the left-most atom from the index of the rhs. It is much like a database join
  set[Atom] mostRightAtomInLhs = {idx.vector[arityLhs - 1] | Index idx <- lhs, idx.theory == relational()};
  
  Binding joinResult = ();
  for (Atom current <- mostRightAtomInLhs) {
    set[Index] lhsIndices = indicesEndingWith(current, lhs, arityLhs);
    set[Index] rhsIndices = indicesStartingWith(current, rhs);
    
    if (lhsIndices != {} && rhsIndices != {}) {  

      for (Index currentLhs <- lhsIndices, Formula lhsVal := lhs[currentLhs], lhsVal != \false(), Index currentRhs <- rhsIndices, Formula rhsVal := rhs[currentRhs], rhsVal != \false()) {
        Formula val = and(lhsVal, rhsVal);
        
        if (val != \false()) {
          Index jointIndex = <relational(), (currentLhs.vector - currentLhs.vector[arityLhs - 1]) + (currentRhs.vector - currentRhs.vector[0])>;

          if (jointIndex notin joinResult) { 
            joinResult[jointIndex] = val;
          } else {
            joinResult[jointIndex] = or(joinResult[jointIndex], val);
          }
        }
      }
    }
  }
  
  return joinResult;
}
  
Binding product(Binding lhs, Binding rhs) 
  = (<relational(), currentLhs.vector + currentRhs.vector> : val | 
      Index currentLhs <- lhs, 
      currentLhs.theory == relational(),
      Index currentRhs <- rhs, 
      Formula val := and(lhs[currentLhs], rhs[currentRhs]), 
      val !:= \false()); 

