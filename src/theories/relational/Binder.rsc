module theories::relational::Binder

extend theories::Binder;

import logic::Propositional;
import theories::relational::AST;
 
import List;
import Map;
import Set;
import IO;

private Binding square(Binding m, int i, int sizeOfUniverse) = m when i >= sizeOfUniverse;
private Binding square(Binding m, int i, int sizeOfUniverse) = or(n, \join(n, n)) when Binding n := square(m, i * 2, sizeOfUniverse); 

private list[Index] constructIdentityIndex(int arity, Universe uni) = [idx | Atom a <- uni.atoms, list[Atom] vector := [a | int _ <- [0..arity]], Index idx := <relTheory(), vector>];

@memo
private Binding identity(Binding orig, Universe uni) = identity(arity(orig), uni);
private Binding identity(int arity, Universe uni) = (idx:\true() | Index idx <- constructIdentityIndex(arity, uni));

private Binding or(Binding lhs, Binding rhs) = (x:\or(lhsVal,rhsVal) | Index x <- (lhs + rhs), x.theory == relTheory(), Formula lhsVal := ((x in lhs) ? lhs[x] : \false()), Formula rhsVal := ((x in rhs) ? rhs[x] : \false())) when sameArity(lhs, rhs);
private default Binding or(Binding _, Binding _) { throw "Unable to perform disjunction of bindings with different arity"; }

private Binding and(Binding lhs, Binding rhs) = (x:\and(lhs[x],rhs[x]) | Index x <- lhs, x.theory == relTheory() , x in rhs) when sameArity(lhs, rhs);
private default Binding and(Binding _, Binding _) { throw "Unable to perform conjunction of bindings with different arity"; }
 
Binding transpose(Binding m, Universe uni) = (() | it + (reversedIndex : m[key]) | Index key <- m, key.theory == relTheory(), Index reversedIndex := <relTheory(), reverse(key.vector)>);

Binding transitiveClosure(Binding m, Universe uni) = square(m, 1, sizeOfUniverse(uni)) when arity(m) == 2;
default Binding transitiveClosure(Binding m, Universe uni) { throw "Can not perform a transitive closure on a non-binary relation"; }

Binding reflexiveTransitiveClosure(Binding m, Universe uni) = or(transitiveClosure(m, uni), identity(m, uni)) when arity(m) == 2; 
default Binding reflexiveTransitiveClosure(Binding m, Universe uni) { throw "Can not perform a reflexive transitive closure on a non-binary relation"; }

Binding disjunction(Binding lhs, Binding rhs) = or(lhs, rhs) when sameArity(lhs, rhs);
default Binding disjunction(Binding lhs, Binding rhs) { throw "Can not perform a disjunction on two relations with different arities"; }  

Binding conjunction(Binding lhs, Binding rhs) = and(lhs, rhs) when sameArity(lhs, rhs);
default Binding conjunction(Binding lhs, Binding rhs) { throw "Can not perform a conjunction on two relations with different arities"; }

Binding difference(Binding lhs, Binding rhs) = (idx:and(lhs[idx], rhsVal) |Index idx <- lhs, idx.theory == relTheory(), Formula rhsVal := ((idx in rhs) ? not(rhs[idx]) : \true())) when sameArity(lhs, rhs);
default Binding different(Binding lhs, Binding rhs) { throw "Can not perform a difference on two relations with different arities"; }  


Binding \join(Binding lhs, Binding rhs) {
  map[Atom, Formula] formulasStartingWith(set[Atom] a, Binding b) {
    map[Atom,Formula] result = ();
    
    for (Index idx <- b, idx.vector[0] in a, b[idx] != \false()) {
      if (idx.vector[0] notin result) { 
        result[idx.vector[0]] = b[idx];
      } else {
        result[idx.vector[0]] = \or(result[idx.vector[0]], b[idx]);
      }
    }
    
    return result;
  }

  map[Atom, Formula] formulasEndingWith(set[Atom] a, Binding b) {
    map[Atom,Formula] result = ();
    
    for (Index idx <- b, idx.vector[-1] in a, b[idx] != \false()) {
      if (idx.vector[-1] notin result) { 
        result[idx.vector[-1]] = b[idx];
      } else {
        result[idx.vector[-1]] = \or(result[idx.vector[-1]], b[idx]);
      }
    }
    
    return result;
  }

    
  Binding j(Binding lhs, Binding rhs, 1, 1) { throw "Unable to join two unary relations"; }
  
  //Binding \join(Binding lhs, Binding rhs, 1, 2) = (<relTheory(),[idx.vector[1]]>:\and(lhs[<relTheory(), [idx.vector[0]]>], rhsFormulas[idx.vector[0]]) |  Index idx <- rhs, idx.vector[0] in lhsAtoms)
  //  when set[Atom] lhsAtoms := {idx.vector[0] | Index idx <- lhs},
  //       map[Atom, Formula] rhsFormulas := formulasStartingWith(lhsAtoms, rhs);
  //
  //Binding \join(Binding lhs, Binding rhs, 2, 1) = (<relTheory(),[idx.vector[0]]>:\and(rhs[<relTheory(), [idx.vector[1]]>], lhsFormulas[idx.vector[1]]) |  Index idx <- lhs, idx.vector[1] in rhsAtoms)
  //  when set[Atom] rhsAtoms := {idx.vector[0] | Index idx <- rhs},
  //       map[Atom, Formula] lhsFormulas := formulasEndingWith(rhsAtoms, lhs);
         
  //Binding \join(Binding lhs, Binding rhs, 2, 2) = ();
  
  default Binding j(Binding lhs, Binding rhs, int arityLhs, int arityRhs) { 
    set[Index] indicesEndingWith(Atom a, Binding b) = {idx | Index idx <- b, idx.theory == relTheory(), idx.vector[-1] == a};
    set[Index] indicesStartingWith(Atom a, Binding b) = {idx | Index idx <- b, idx.theory == relTheory(), idx.vector[0] == a};

    // join by joining the right-most atom from the index of the lhs with the left-most atom from the index of the rhs. It is much like a database join
    set[Atom] mostRightAtomInLhs = {idx.vector[-1] | Index idx <- lhs, idx.theory == relTheory()};
    
    Binding joinResult = ();
    for (Atom current <- mostRightAtomInLhs) {
      set[Index] lhsIndices = indicesEndingWith(current, lhs);
      set[Index] rhsIndices = indicesStartingWith(current, rhs);
      
      if (lhsIndices != {} && rhsIndices != {}) {  
  
        for (Index currentLhs <- lhsIndices, Formula lhsVal := lhs[currentLhs], lhsVal != \false(), Index currentRhs <- rhsIndices, Formula rhsVal := rhs[currentRhs], rhsVal != \false()) {
          Formula val = and(lhsVal, rhsVal);
          
          if (val != \false()) {
            Index jointIndex = <relTheory(), (currentLhs.vector - currentLhs.vector[arityLhs - 1]) + (currentRhs.vector - currentRhs.vector[0])>;
  
            if (jointIndex notin joinResult) { 
              joinResult[jointIndex] = val;
            } else if (joinResult[jointIndex] == \true()) {
              break;
            }else {
              joinResult[jointIndex] = or(joinResult[jointIndex], val);
            }
          }
        }
      }
    }
    
    return joinResult;
  }
  
  return j(lhs, rhs, arity(lhs), arity(rhs));
}
  
Binding product(Binding lhs, Binding rhs) 
  = (<relTheory(), currentLhs.vector + currentRhs.vector> : val | 
      Index currentLhs <- lhs, 
      lhs[currentLhs] != \false(),
      currentLhs.theory == relTheory(),
      Index currentRhs <- rhs, 
      rhs[currentRhs] != \false(),
      currentRhs.theory == relTheory(),
      Formula val := and(lhs[currentLhs], rhs[currentRhs]), 
      val !:= \false()); 

