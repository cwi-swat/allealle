module theories::Binder

import logic::Propositional;
import theories::AST;

import List;
import Map;
import Set;
import IO;

alias ExtensionEncoding = map[int, Formula];
alias TheoryExtension = map[Theory, ExtensionEncoding]; 
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

Content construct(Formula f, TheoryExtension ext) = <f, ext>;

TheoryExtension merge(TheoryExtension lhs, TheoryExtension rhs) {
  TheoryExtension result = (t:lhs[t] | Theory t <- lhs, t notin rhs) + (t:rhs[t] | Theory t <- rhs, t notin lhs);
  
  for (Theory t <- (lhs + rhs), t in lhs && t in rhs) {
    ExtensionEncoding merged = (); 
    
    for (int i <- lhs[t]) {
      if (i in rhs[t], lhs[t][i] != rhs[t][i]) {
          throw "Unable to merge theory extensions, both relations encode theory variable but have different variable on the same position (<i>). Lhs has \'<lhs[t][i]>\' while rhs has \'<rhs[t][i]>\'";
      }
        
      merged[i] = lhs[t][i];
    }
    
    for (int i <- rhs[t], i notin lhs[t]) {
      merged[i] = rhs[t][i];
    }
    
    result[t] = merged;
  }
  
  return result;
} 

private bool p(RelationMatrix m) { println("Printing matrix:"); iprintln(m); return true;}

private RelationMatrix square(RelationMatrix m, int i, int sizeOfUniverse) = m when i >= sizeOfUniverse;
private RelationMatrix square(RelationMatrix m, int i, int sizeOfUniverse) = or(n, \join(n, n)) when RelationMatrix n := square(m, i * 2, sizeOfUniverse); 

private list[Index] constructIdentityIndex(int arity, Universe uni) = [vector | AtomDecl ad <- uni.atoms, list[Atom] vector := [ad.atom | int _ <- [0..arity]]];

@memo
RelationMatrix identity(RelationMatrix orig, Universe uni) = identity(arity(orig), uni);
RelationMatrix identity(int arity, Universe uni) = (idx:<\true(),()> | Index idx <- constructIdentityIndex(arity, uni));

RelationMatrix or(RelationMatrix lhs, RelationMatrix rhs) 
  = (x:<\or(lhsVal,rhsVal), merge(lhsExt, rhsExt)> | Index x <- (lhs + rhs), Formula lhsVal := ((x in lhs) ? lhs[x].relForm : \false()), Formula rhsVal := ((x in rhs) ? rhs[x].relForm : \false()), TheoryExtension lhsExt := ((x in lhs) ? lhs[x].ext : ()), TheoryExtension rhsExt := ((x in rhs) ? rhs[x].ext : ())) 
  when sameArity(lhs, rhs);
default RelationMatrix or(RelationMatrix _, RelationMatrix _) { throw "Unable to perform disjunction of bindings with different arity"; }

RelationMatrix and(RelationMatrix lhs, RelationMatrix rhs) = (x:construct(\and(lhs[x].relForm, rhs[x].relForm), merge(lhs[x].ext, rhs[x].ext)) | Index x <- lhs, x in rhs) when sameArity(lhs, rhs);
default RelationMatrix and(RelationMatrix _, RelationMatrix _) { throw "Unable to perform conjunction of bindings with different arity"; }
 
private TheoryExtension transposeTheoryExtension(TheoryExtension ext, int arity) = (t : (arity - 1 - i : ext[t][i] | int i <- ext[t]) | Theory t <- ext); 

RelationMatrix transpose(RelationMatrix m) = (() | it + (reversedIndex : <m[key].relForm, transposeTheoryExtension(m[key].ext, arity(m))>) | Index key <- m, Index reversedIndex := reverse(key));

RelationMatrix transitiveClosure(RelationMatrix m, Universe uni) = square(m, 1, sizeOfUniverse(uni)) when arity(m) == 2;
default RelationMatrix transitiveClosure(RelationMatrix m, Universe uni) { throw "Can not perform a transitive closure on a non-binary relation"; }

RelationMatrix reflexiveTransitiveClosure(RelationMatrix m, Universe uni) = or(transitiveClosure(m, uni), identity(m, uni)) when arity(m) == 2; 
default RelationMatrix reflexiveTransitiveClosure(RelationMatrix m, Universe uni) { throw "Can not perform a reflexive transitive closure on a non-binary relation"; }

RelationMatrix disjunction(RelationMatrix lhs, RelationMatrix rhs) = or(lhs, rhs) when sameArity(lhs, rhs);
RelationMatrix conjunction(RelationMatrix lhs, RelationMatrix rhs) = and(lhs, rhs) when sameArity(lhs, rhs);

RelationMatrix difference(RelationMatrix lhs, RelationMatrix rhs) = (idx:construct(and(lhs[idx].relForm, rhsVal), lhs[idx].ext) | Index idx <- lhs, Formula rhsVal := ((idx in rhs) ? not(rhs[idx].relForm) : \true())) 
  when sameArity(lhs, rhs);
default RelationMatrix difference(RelationMatrix lhs, RelationMatrix rhs) { throw "Can not perform a difference on two relations with different arities"; }  

RelationMatrix \join(RelationMatrix lhs, RelationMatrix rhs) {
  int arityLhs = arity(lhs);
  int arityRhs = arity(rhs);
    
  if (arityLhs == 1 && arityRhs == 1) { throw "Unable to join two unary relations"; }

  TheoryExtension compose(TheoryExtension current, TheoryExtension lhsExt, TheoryExtension rhsExt) = () 
    when current == (), lhsExt == (), rhsExt == ();
  TheoryExtension compose(TheoryExtension current, TheoryExtension lhsExt, TheoryExtension rhsExt) = (t : (i:lhsExt[t][i] | int i <- [0..arityLhs-1], i in lhsExt[t]) | Theory t <- lhsExt) 
    when current == (), lhsExt != (), rhsExt == ();
  TheoryExtension compose(TheoryExtension current, TheoryExtension lhsExt, TheoryExtension rhsExt) = (t : (i-1:rhsExt[t][i] | int i <- [1..arityRhs], i in rhsExt[t]) | Theory t <- rhsExt) 
    when current == (), lhsExt == (), rhsExt != ();
  TheoryExtension compose(TheoryExtension current, TheoryExtension lhsExt, TheoryExtension rhsExt) = (t : compLhs[t] + (i + arityLhs - 1 : compRhs[t][i] | int i <- compRhs[t]) | Theory t <- compLhs)  
    when current == (), lhsExt != (), rhsExt != (), TheoryExtension compLhs := compose((), lhsExt, ()), TheoryExtension compRhs := compose((), (), rhsExt);
  
  TheoryExtension compose(TheoryExtension current, TheoryExtension lhsExt, TheoryExtension rhsExt) = current 
    when current != (), lhsExt != (), rhsExt == (), compose((), lhsExt, ()) == current;
  TheoryExtension compose(TheoryExtension current, TheoryExtension lhsExt, TheoryExtension rhsExt) = current 
    when current != (), lhsExt == (), rhsExt != (), compose((), (), rhsExt) == current;
  TheoryExtension compose(TheoryExtension current, TheoryExtension lhsExt, TheoryExtension rhsExt) = current
    when current != (), lhsExt != (), rhsExt != (), compose((), lhsExt, rhsExt) == current;
      
  default TheoryExtension compose(TheoryExtension current, TheoryExtension lhsExt, TheoryExtension rhsExt) { throw "Unable to compose theory extensions, current values: \'<current>\', lhs values: \'<lhsExt>\', rhs values: \'<rhsExt>\'";}    
      
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
          Index jointIndex = (currentLhs - currentLhs[-1]) + (currentRhs - currentRhs[0]);

          if (jointIndex notin joinResult) { 
            joinResult[jointIndex] = <val, compose((), lhs[currentLhs].ext, rhs[currentRhs].ext)>;
          }else {
            joinResult[jointIndex] = <or(joinResult[jointIndex].relForm, val), compose(joinResult[jointIndex].ext, lhs[currentLhs].ext, rhs[currentRhs].ext)>;
          }
        }
      }
    }
  }
  
  //println("After join");
  //p(joinResult);
  //  
  return joinResult;
}

TheoryExtension productTheoryExtension(int arityLhs, TheoryExtension lhs, TheoryExtension rhs) =
  lhs + (t : (i + arityLhs : rhs[t][i] | int i <- rhs[t]) | Theory t <- rhs);

RelationMatrix product(RelationMatrix lhs, RelationMatrix rhs) 
  = (currentLhs + currentRhs : <val, productTheoryExtension(arityLhs, lhs[currentLhs].ext, rhs[currentRhs].ext)> | 
      Index currentLhs <- lhs, 
      lhs[currentLhs].relForm != \false(),
      int arityLhs := arity(lhs),
      Index currentRhs <- rhs, 
      rhs[currentRhs].relForm != \false(),
      Formula val := and(lhs[currentLhs].relForm, rhs[currentRhs].relForm), 
      val !:= \false()); 


 

