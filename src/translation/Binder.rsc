module translation::Binder

import logic::Propositional;
import translation::AST;

import List;
import Map;
import Set;
import IO;

alias Index = list[Id]; 

alias IdDomain = set[Id]; 

data Cell 
  = relOnly(Formula relForm)
  | relAndAtt(Formula relForm, Formula attForm)
  ;

alias RelationMatrix = map[Index, Cell];

alias Environment = tuple[map[str, RelationMatrix] relations, map[Index, map[str, Formula]] attributes, list[Id] idDomain]; 

int sizeOfIdDomain(IdDomain idd) = size(idd);

int arity(RelationMatrix rm) = 0 when rm == ();
default int arity(RelationMatrix rm) = size(getOneFrom(rm));

private bool sameArity(RelationMatrix lhs, RelationMatrix rhs) = arity(lhs) == arity(rhs); 

@memo 
RelationMatrix universe(Environment env) = ([id] : relOnly(\true()) | Id id <- env.idDomain);

@memo
RelationMatrix identity(Environment env) = ([id,id] : relOnly(\true()) | Id id <- env.idDomain);

RelationMatrix or(RelationMatrix lhs, RelationMatrix rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "OR only works on relations of same arity";
  }
  
  return (idx : relOnly(\or(lhsVal, rhsVal)) | Index idx <- (lhs + rhs), Formula lhsVal := ((idx in lhs) ? lhs[idx].relForm : \false()), Formula rhsVal := ((idx in rhs) ? rhs[idx].relForm : \false()));
}

RelationMatrix and(RelationMatrix lhs, RelationMatrix rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "AND only works on relations of same arity";
  }
  
  return (idx : relOnly(\and(lhs[idx].relForm, rhs[idx].relForm)) | Index idx <- lhs, idx in rhs, lhs[idx].relForm != \false(), rhs[idx].relForm != \false());
}

RelationMatrix transpose(RelationMatrix m) {
  if (arity(m) != 2) {
    throw "TRANSPOSE only works on binary relations";
  }
  
  return (reverse(idx) : m[idx] | Index idx <- m);
} 

RelationMatrix transitiveClosure(RelationMatrix m) {
  if (arity(m) != 2) {
    throw "TRANSITIVE CLOSURE only works on binary relations";
  }
  
  int rows = size({a | [Id a, Id _] <- m}); 

  RelationMatrix ret = m;
  int i = 1;
  while(i < rows) {
    ret = or(ret, dotJoin(ret,ret));
    i *= 2;
  }
  
  return ret;
}

RelationMatrix reflexiveTransitiveClosure(RelationMatrix m, Environment env) {
  if (arity(m) != 2) {
    throw "REFLEXIVE TRANSITIVE CLOSURE only works on binary relations";
  }
  
  return or(transitiveClosure(m), identity(env));
} 

RelationMatrix difference(RelationMatrix lhs, RelationMatrix rhs) {
  if (!sameArity(lhs,rhs)) {
    throw "DIFFERENCE only works on relations of same arity";
  }
  
  return (idx : relOnly(\and(lhs[idx].relForm, rhsVal)) | Index idx <- lhs, Formula rhsVal := ((idx in rhs) ? not(rhs[idx].relForm) : \true()));
} 

//@memo
RelationMatrix dotJoin(RelationMatrix lhs, RelationMatrix rhs) {
  int arityLhs = arity(lhs);
  int arityRhs = arity(rhs);
    
  if (arityLhs == 1 && arityRhs == 1) { 
    throw "JOIN only works on two non-unary relations"; 
  }
  
  if (lhs == () || rhs == ()) {
    return ();
  }
        
  set[Index] indicesEndingWith(Id a, RelationMatrix b) = {idx | Index idx <- b, idx[-1] == a};
  set[Index] indicesStartingWith(Id a, RelationMatrix b) = {idx | Index idx <- b, idx[0] == a};

  set[Id] mostRightIdInLhs = {idx[-1] | Index idx <- lhs};
    
  RelationMatrix relResult = ();
  for (Id current <- mostRightIdInLhs) {
    set[Index] lhsIndices = indicesEndingWith(current, lhs);
    set[Index] rhsIndices = indicesStartingWith(current, rhs);
    
    for (Index lhsIdx <- lhsIndices, lhs[lhsIdx].relForm != \false(), Index rhsIdx <- rhsIndices, rhs[rhsIdx].relForm != \false()) {
      Formula val = and(lhs[lhsIdx].relForm, rhs[rhsIdx].relForm);
      
      if (val != \false()) {
        Index joinIdx = (lhsIdx - lhsIdx[-1]) + (rhsIdx - rhsIdx[0]);
        if (val == \true()) {
          relResult[joinIdx] = relOnly(\true());
        } else if (joinIdx in relResult, relResult[joinIdx].relForm != \true()) {
          relResult[joinIdx] = relOnly(\or(relResult[joinIdx].relForm, val));
        } else {        
          relResult[joinIdx] = relOnly(val);
        }
      }
    }
  }
   
  return relResult;
}

RelationMatrix product(RelationMatrix lhs, RelationMatrix rhs) 
 = (lIdx + rIdx : relOnly(\and(lhs[lIdx].relForm, rhs[rIdx].relForm)) | Index lIdx <- lhs, lhs[lIdx].relForm != \false(), Index rIdx <- rhs, rhs[rIdx].relForm != \false());

//@memo
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
