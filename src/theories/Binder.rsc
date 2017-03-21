module theories::Binder

import logic::Propositional;
import theories::AST;

import List;
import Map;
import Set;
import IO;

alias TheoryExtension = map[Theory, set[Formula]]; 
alias Content = tuple[Formula relForm,  TheoryExtension ext];
alias Index = list[Atom]; 
alias RelationMatrix = map[Index, Content];

alias Environment = map[str, RelationMatrix];

@memo
int sizeOfUniverse(Universe u) = size(u.atoms);

@memo
int arity(RelationMatrix rm) {
  return size(getOneFrom(rm));
}

@memo
private bool sameArity(RelationMatrix lhs, RelationMatrix rhs) = arity(lhs) == arity(rhs); 

private Content construct(Formula f, TheoryExtension ext) = <f, ext>;
private TheoryExtension merge(TheoryExtension lhs, TheoryExtension rhs) = lhs + rhs;

private RelationMatrix square(RelationMatrix m, int i, int sizeOfUniverse) = m when i >= sizeOfUniverse;
private RelationMatrix square(RelationMatrix m, int i, int sizeOfUniverse) = or(n, \join(n, n)) when RelationMatrix n := square(m, i * 2, sizeOfUniverse); 

private list[Index] constructIdentityIndex(int arity, Universe uni) = [vector | AtomDecl ad <- uni.atoms, list[Atom] vector := [ad.atom | int _ <- [0..arity]]];

@memo
private RelationMatrix identity(RelationMatrix orig, Universe uni) = identity(arity(orig), uni);
private RelationMatrix identity(int arity, Universe uni) = (idx:<\true(),()> | Index idx <- constructIdentityIndex(arity, uni));

private RelationMatrix or(RelationMatrix lhs, RelationMatrix rhs) = (x:construct(\or(lhsVal,rhsVal), merge(lhsExt, rhsExt)) | Index x <- (lhs + rhs), Formula lhsVal := ((x in lhs) ? lhs[x].relForm : \false()), Formula rhsVal := ((x in rhs) ? rhs[x].relForm : \false()), TheoryExtension lhsExt := ((x in lhs) ? lhs[x].ext : ()), TheoryExtension rhsExt := ((x in rhs) ? rhs[x].ext : ())) 
  when sameArity(lhs, rhs);
private default RelationMatrix or(RelationMatrix _, RelationMatrix _) { throw "Unable to perform disjunction of bindings with different arity"; }

private RelationMatrix and(RelationMatrix lhs, RelationMatrix rhs) = (x:construct(\and(lhs[x].relForm, rhs[x].relForm), merge(lhs[x].ext, rhs[x].ext)) | Index x <- lhs, x in rhs) when sameArity(lhs, rhs);
private default RelationMatrix and(RelationMatrix _, RelationMatrix _) { throw "Unable to perform conjunction of bindings with different arity"; }
 
RelationMatrix transpose(RelationMatrix m) = (() | it + (reversedIndex : m[key]) | Index key <- m, Index reversedIndex := reverse(key));

RelationMatrix transitiveClosure(RelationMatrix m, Universe uni) = square(m, 1, sizeOfUniverse(uni)) when arity(m) == 2;
default RelationMatrix transitiveClosure(RelationMatrix m, Universe uni) { throw "Can not perform a transitive closure on a non-binary relation"; }

RelationMatrix reflexiveTransitiveClosure(RelationMatrix m, Universe uni) = or(transitiveClosure(m, uni), identity(m, uni)) when arity(m) == 2; 
default RelationMatrix reflexiveTransitiveClosure(RelationMatrix m, Universe uni) { throw "Can not perform a reflexive transitive closure on a non-binary relation"; }

RelationMatrix disjunction(RelationMatrix lhs, RelationMatrix rhs) = or(lhs, rhs) when sameArity(lhs, rhs);
RelationMatrix conjunction(RelationMatrix lhs, RelationMatrix rhs) = and(lhs, rhs) when sameArity(lhs, rhs);

RelationMatrix difference(RelationMatrix lhs, RelationMatrix rhs) = (idx:construct(and(lhs[idx].relForm, rhsVal), lhs[idx].ext) | Index idx <- lhs, Formula rhsVal := ((idx in rhs) ? not(rhs[idx].relForm) : \true())) 
  when sameArity(lhs, rhs);
default RelationMatrix different(RelationMatrix lhs, RelationMatrix rhs) { throw "Can not perform a difference on two relations with different arities"; }  


RelationMatrix \join(RelationMatrix lhs, RelationMatrix rhs) {
  map[Atom, Formula] formulasStartingWith(set[Atom] a, RelationMatrix b) {
    map[Atom,Formula] result = ();
    
    for (Index idx <- b, idx[0] in a, b[idx].relForm != \false()) {
      if (idx[0] notin result) { 
        result[idx[0]] = b[idx].relForm;
      } else {
        result[idx[0]] = \or(result[idx[0]], b[idx].relForm);
      }
    }
    
    return result;
  }

  map[Atom, Formula] formulasEndingWith(set[Atom] a, RelationMatrix b) {
    map[Atom,Formula] result = ();
    
    for (Index idx <- b, idx[-1] in a, b[idx].relForm != \false()) {
      if (idx[-1] notin result) { 
        result[idx[-1]] = b[idx].relForm;
      } else {
        result[idx[-1]] = \or(result[idx[-1]], b[idx].relForm);
      }
    }
    
    return result;
  }

    
  RelationMatrix j(RelationMatrix lhs, RelationMatrix rhs, 1, 1) { throw "Unable to join two unary relations"; }
  
  //Binding \join(Binding lhs, Binding rhs, 1, 2) = (<relTheory(),[idx.vector[1]]>:\and(lhs[<relTheory(), [idx.vector[0]]>], rhsFormulas[idx.vector[0]]) |  Index idx <- rhs, idx.vector[0] in lhsAtoms)
  //  when set[Atom] lhsAtoms := {idx.vector[0] | Index idx <- lhs},
  //       map[Atom, Formula] rhsFormulas := formulasStartingWith(lhsAtoms, rhs);
  //
  //Binding \join(Binding lhs, Binding rhs, 2, 1) = (<relTheory(),[idx.vector[0]]>:\and(rhs[<relTheory(), [idx.vector[1]]>], lhsFormulas[idx.vector[1]]) |  Index idx <- lhs, idx.vector[1] in rhsAtoms)
  //  when set[Atom] rhsAtoms := {idx.vector[0] | Index idx <- rhs},
  //       map[Atom, Formula] lhsFormulas := formulasEndingWith(rhsAtoms, lhs);
         
  //Binding \join(Binding lhs, Binding rhs, 2, 2) = ();

  TheoryExtension compose(TheoryExtension lhsExt, TheoryExtension rhsExt) {
    TheoryExtension result = ();
    
    //for (Theory curT <- rhsExt) {
    //  if (curT notin lhsExt) {
    //    result[curT] = rhsExt[curT];
    //  }
    //  else {
    //    result[curT] = lhsExt[curT] + rhsExt[curT] - (lhsExt[curT] & rhsExt[curT]);
    //  }
    //}
    
    result = lhsExt + rhsExt;
        
    return result;
  } 
  
  default RelationMatrix j(RelationMatrix lhs, RelationMatrix rhs, int arityLhs, int arityRhs) { 
    set[Index] indicesEndingWith(Atom a, RelationMatrix b) = {idx | Index idx <- b, idx[-1] == a};
    set[Index] indicesStartingWith(Atom a, RelationMatrix b) = {idx | Index idx <- b, idx[0] == a};

    // join by joining the right-most atom from the index of the lhs with the left-most atom from the index of the rhs. It is much like a database join
    set[Atom] mostRightAtomInLhs = {idx[-1] | Index idx <- lhs};
    
    RelationMatrix joinResult = ();
    for (Atom current <- mostRightAtomInLhs) {
      set[Index] lhsIndices = indicesEndingWith(current, lhs);
      set[Index] rhsIndices = indicesStartingWith(current, rhs);
      
      if (lhsIndices != {} && rhsIndices != {}) {  
  
        for (Index currentLhs <- lhsIndices, Formula lhsVal := lhs[currentLhs].relForm, lhsVal != \false(), Index currentRhs <- rhsIndices, Formula rhsVal := rhs[currentRhs].relForm, rhsVal != \false()) {
          Formula val = and(lhsVal, rhsVal);
          
          if (val != \false()) {
            Index jointIndex = currentLhs - currentLhs[arityLhs - 1] + currentRhs - currentRhs[0];
  
            if (jointIndex notin joinResult) { 
              joinResult[jointIndex] = construct(val, compose(lhs[currentLhs].ext, rhs[currentRhs].ext));
            } else if (joinResult[jointIndex].relForm == \true()) {
              break;
            }else {
              joinResult[jointIndex] = construct(or(joinResult[jointIndex].relForm, val), compose(lhs[currentLhs].ext, rhs[currentRhs].ext));
            }
          }
        }
      }
    }
    
    return joinResult;
  }
  
  return j(lhs, rhs, arity(lhs), arity(rhs));
}
  
RelationMatrix product(RelationMatrix lhs, RelationMatrix rhs) 
  = (currentLhs + currentRhs : construct(val, merge(lhs[currentLhs].ext, rhs[currentRhs].ext)) | 
      Index currentLhs <- lhs, 
      lhs[currentLhs].relForm != \false(),
      Index currentRhs <- rhs, 
      rhs[currentRhs].relForm != \false(),
      Formula val := and(lhs[currentLhs].relForm, rhs[currentRhs].relForm), 
      val !:= \false()); 


 

