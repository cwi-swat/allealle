module translation::Relation

import smtlogic::Core;
import translation::AST;

import List;
import Map;
import Set;
import IO;

import util::Benchmark;

//alias AdditionalConstraintFunctions = tuple[void (Formula) addAttributeConstraint, void (Command) addAdditionalCommand, void (Formula) addIntermediateVar, Id () freshIntermediateId]; 

alias Header = map[str,Domain];

alias Key = map[str,Cell];
alias Attributes = map[str,Cell];

alias Relation = tuple[Header header, map[Key,Attributes] rows];

str formulaCol() = "_formula";
str constraintsCol() = "_constraints";
set[str] addedCols() = {formulaCol(), constraintsCol()};

data Cell 
  = key(str k)
  | formula(Formula form)
  | term(Term t)
  ;

Formula getFormula(Attributes r) = f when formula(Formula f) := r[formulaCol()];
Formula getConstraints(Attributes r) = f when formula(Formula f) := r[constraintsCol()];

bool isFalse(Attributes r) = getFormula(r) == \false(); 

@memo
set[str] getIdFieldsFromHeader(Header h) = {n | str n <- h, h[n] == id()}; 

int arityOfIds(Relation rm) = size(getIdFieldsFromHeader(rm.header));

bool sameArityOfIds(Relation lhs, Relation rhs) = arityOfIds(lhs) == arityOfIds(rhs); 

@memo
set[Key] getKeys(Relation m) = m.rows<0>; 

bool unionCompatible(Relation lhs, Relation rhs) {
  for (str att <- lhs.header, att notin rhs.header || lhs.header[att] != rhs.header[att]) {
    return false;
  } 
  
  return true;
}

@memo
Attributes initRow() = (constraintsCol():formula(\true()));

Attributes combineRows(Attributes r1, Attributes r2, Formula (Formula,Formula) formOp) {
  Attributes combined = initRow();

  bool addConstraint(Formula c) { combined[constraintsCol()] = formula(\and(getConstraints(combined), c)); return true;} 

  Cell combineAtt(t1:term(v:var(_,_)), t2:term(l:lit(_))) = e2 when addConstraint(\equal(v,l));
  Cell combineAtt(t1:expr(l:lit(_)), t2:term(v:var(_,_))) = e1 when addConstraint(\equal(v,l));
  Cell combineAtt(t:term(_), t) = e;
  default Cell combinedAtt(Cell c1, Cell c2) { throw "Unable to combine \'<c1>\' with \'<c2>\'"; } 

  set[str] allAttributes = r1<0> + r2<0>;

  for (str att <- allAttributes) {
    if (att == formulaCol()) {
      combined[formulaCol()] = formula(formOp(getFormula(r1), getFormula(r2)));
    } else if (att == constraintsCol()) {
      combined[constraintsCol()] = formula(\and({getConstraints(combined), getConstraints(r1), getConstraints(r2)}));
    } else if (att in r1 && att in r2) {
      combined[att] = combineAtt(r1[att],r2[att]);
    } else if (att in r1) { 
      combined[att] = r1[att];
    } else {
      combined[att] = r2[att];
    }
  }
  
  return combined;
} 

@memo
Relation union(Relation lhs, Relation rhs) {
  if (!unionCompatible(lhs,rhs)) {
    throw "UNION only works on union compatible relations";
  }

  if (rhs.rows == ()) {
    return lhs;
  } else if (lhs.rows == ()) {
    return rhs;
  }
   
  map[Key, Attributes] rows = ();
  
  set[Key] lhsKeys = getKeys(lhs);
  set[Key] rhsKeys = getKeys(rhs);

  for (Key key <- (lhsKeys + rhsKeys)) {
    Attributes row = ();
    
    if (key in lhsKeys && key in rhsKeys) {
      row = combineRows(lhs.rows[key], rhs.rows[key], Formula (Formula l, Formula r) {return \or(l,r);});
    } else if (key in lhsKeys) {
      row = lhs.rows[key];
    } else {
      row = rhs.rows[key];
    }
    
    rows[key] = row;
  }  
   
  return <lhs.header, rows>; 
}
 
@memo
Relation intersection(Relation lhs, Relation rhs) {
  if (!unionCompatible(lhs,rhs)) {
    throw "INTERSECTION only works on union compatible relations";
  }

  if (lhs.rows == () || rhs.rows == ()) {
    return lhs;
  }

  map[Key,Attributes] rows = ();
  
  set[Key] lhsKeys = getKeys(lhs);
  set[Key] rhsKeys = getKeys(rhs);
  
  for (Key key <- lhsKeys, key in rhsKeys, !isFalse(lhs.rows[key]), !isFalse(rhs.rows[key])) {
    Attributes r = combineRows(lhs.rows[key], rhs.rows[key]);
    r[formulaCol()] = formula(\and(getFormula(lhs.rows[key]), getFormula(rhs.rows[key])));    
  
    rows[key] = r;
  } 
  
  return <lhs.header, lhs.primKeys, rebuildIndices(rows), rows>;
}

@memo
Relation override(Relation lhs, Relation rhs) {
  if (rhs == ()) {
    return lhs;
  } else if (lhs == ()) {
    return rhs;
  }

  if (!sameArity(lhs,rhs)) {
    throw "OVERRIDE only works on relations of same arity";
  }

  map[Id, set[Index]] lhsRows = ();
  for (Index idx <- lhs) {
    lhsRows[idx[0]] = (idx[0] in lhsRows) ? lhsRows[idx[0]] + idx : {idx};
  }

  map[Id, Formula] rhsNandForm = ();
  for (Index idx <- rhs, idx[0] in lhsRows) {
    rhsNandForm[idx[0]] = (idx[0] in rhsNandForm) ? and(rhsNandForm[idx[0]], not(rhs[idx].relForm)) : not(rhs[idx].relForm); 
  }
    
  Relation result = rhs;
  
  for (Id i <- lhsRows, Index idx <- lhsRows[i]) {
    Formula current = (idx in result) ? result[idx].relForm : \false();
    Formula nand = (i in rhsNandForm) ? rhsNandForm[i] : \true();
     
    result[idx] = relOnly(or(current, and(lhs[idx].relForm, nand)));
  } 
  
  return result;
}

@memo
Relation transitiveClosure(Relation m) {
  if (arity(m) != 2) {
    throw "TRANSITIVE CLOSURE only works on binary relations";
  }
  
  int rows = size({idx[0] | Index idx <- m}); 

  Relation ret = m;
  int i = 1;
  while(i < rows) {
    ret = or(ret, dotJoin(ret,ret));
    i *= 2;
  } 
  
  return ret; 
}

@memo
Relation reflexiveTransitiveClosure(Relation m, Relation iden) {
  if (arity(m) != 2) {
    throw "REFLEXIVE TRANSITIVE CLOSURE only works on binary relations";
  }
  
  return or(transitiveClosure(m), iden); 
} 

@memo
Relation difference(Relation lhs, Relation rhs) {
  if (lhs == ()) {
    return ();
  } else if (rhs == ()) {
    return lhs;
  }
  
  if (!sameArity(lhs,rhs)) {
    throw "DIFFERENCE only works on relations of same arity";
  }
  
  return (idx : relOnly(\and(lhs[idx].relForm, rhsVal)) | Index idx <- lhs, Formula rhsVal := ((idx in rhs) ? not(rhs[idx].relForm) : \true()));
} 

@memo
Relation dotJoin(Relation lhs, Relation rhs) {
  int arityLhs = arity(lhs);
  int arityRhs = arity(rhs);
    
  if (arityLhs == 1 && arityRhs == 1) { 
    throw "JOIN only works on two non-unary relations"; 
  }
  
  if (lhs == () || rhs == ()) {
    return ();
  }

  set[Index] indicesEndingWith(Id a, Relation b) = {idx | Index idx <- b, idx[-1] == a};
  set[Index] indicesStartingWith(Id a, Relation b) = {idx | Index idx <- b, idx[0] == a};
  
  set[Id] joiningIds;
  if (size(lhs) < size(rhs)) {
    joiningIds = {idx[-1] | Index idx <- lhs};
  } else {
    joiningIds = {idx[0] | Index idx <- rhs};
  }
  map[Id, set[Index]] lhsEndingWith = (b : indicesEndingWith(b,lhs) | Id b <- joiningIds);    
  map[Id, set[Index]] rhsStartingWith = (b : indicesStartingWith(b,rhs) | Id b <- joiningIds);    

  Relation relResult = ();
  for (Id current <- joiningIds, Index lhsIdx <- lhsEndingWith[current], lhs[lhsIdx].relForm != \false(), Index rhsIdx <- rhsStartingWith[current], rhs[rhsIdx].relForm != \false()) {
    Formula val = and(lhs[lhsIdx].relForm, rhs[rhsIdx].relForm);
    
    if (val != \false()) {
      Index joinIdx = (lhsIdx - lhsIdx[-1]) + (rhsIdx - rhsIdx[0]);
      if (val == \true()) {
        relResult[joinIdx] = relOnly(\true());
      } else if (joinIdx in relResult) {
          if (relResult[joinIdx].relForm != \true()) {
            relResult[joinIdx] = relOnly(\or(relResult[joinIdx].relForm, val));
          }
      } else {        
        relResult[joinIdx] = relOnly(val);
      }
    }
  }

  return relResult;
}

@memo
Relation product(Relation lhs, Relation rhs) 
 = (lIdx + rIdx : relOnly(\and(lhs[lIdx].relForm, rhs[rIdx].relForm)) | Index lIdx <- lhs, lhs[lIdx].relForm != \false(), Index rIdx <- rhs, rhs[rIdx].relForm != \false());

@memo
Relation ite(Formula \case, Relation \then, Relation \else) {
  if (arity(then) != arity(\else)) {
    throw "Arity of relation in THEN must be equal to the arity of the relation in ELSE for the ITE to work";
  }

  if (\case == \true()) {
    return then;
  } else if (\case == \false()) {
    return \else;
  } 
  
  Relation relResult = ();
  
  for (Index idx <- (then + \else)) {
    Formula thenRel = ((idx in then) ? then[idx].relForm : \false());
    Formula elseRel = ((idx in \else) ? \else[idx].relForm : \false()); 
    
    relResult[idx] = relOnly(ite(\case, thenRel, elseRel));
  } 
  
  return relResult;
}
