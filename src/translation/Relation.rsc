module translation::Relation

import smtlogic::Core;
import translation::AST;

import List;
import Map;
import Set;
import IO;

import util::Benchmark;

alias Heading = map[str,Domain];

alias Rows = map[Tuple, Constraints];
alias Row = tuple[Tuple values, Constraints constraints];
alias Constraints = tuple[Formula exists, Formula attConstraints];

alias Tuple = map[str,Term];

alias Relation = tuple[Heading heading, Rows rows, set[str] partialKey];

alias IndexedRows = tuple[set[str] partialKey, lrel[Tuple partialKey, Row row] indexedRows];

bool isPresent(Constraints c) = c.exists != \false() && c.attConstraints != \false(); 

Formula together(Constraints c) = \and(c.exists,c.attConstraints);

Formula getAttributeConstraints(Constraints c) = implies(c.exists, c.attConstraints);

bool isFixed(var(_,_)) = false;
default bool isFixed(Term _) = true;

bool sameArity(Relation r1, Relation r2) = size(r1.heading) == size(r2.heading); 

IndexedRows index(Rows rows, set[str] partialKey)
  = <partialKey, [<getPartialKeyTuple(row, partialKey), <row, rows[row]>> | Tuple row <- rows]>;

IndexedRows index(Relation r) = index(r.rows, r.partialKey);

Relation toRelation(IndexedRows rows, Heading heading)
  = <heading, (k.row.values : k.row.constraints | k <- rows.indexedRows), rows.partialKey>;
  
Tuple getPartialKeyTuple(Tuple row, set[str] partialKey) = (att : row[att] | str att <- row, att in partialKey);

set[str] getIdFields(Heading h) = {f | str f <- h, h[f] == id()}; 
  
bool unionCompatible(Relation r1, Relation r2) = r1.heading == r2.heading; 

bool isEmpty(Relation r) = r.rows == ();

IndexedRows addRow(IndexedRows current, Row new) {
  if (!isPresent(new.constraints)) {
    return current;
  }
  
  Tuple newPartialKeyTuple = getPartialKeyTuple(new.values, current.partialKey);
  
  if (newPartialKeyTuple notin current.indexedRows.partialKey) {
    return <current.partialKey, current.indexedRows + <newPartialKeyTuple, new>>;
  }
  
  set[str] openAttributes = new.values<0> - current.partialKey;
  
  bool mergedRows = false;
  
  Formula constraintsForm = new.constraints.attConstraints;
  for (Row r <- current.indexedRows[newPartialKeyTuple]) {
    Formula tmpAttForm = \true();
    
    for (str att <- openAttributes) {
      tmpAttForm = \and(tmpAttForm, equal(r.values[att], new.values[att]));
    }
    
    if (tmpAttForm != \true()) {
      constraintsForm = \and(constraintsForm, implies(r.constraints.exists, not(tmpAttForm)));
    } else {
      // Attributes are equal or non-existing, so same row. Merge 'present' formula's
      current.indexedRows = current.indexedRows - <newPartialKeyTuple,r> + <newPartialKeyTuple, <r.values, <\or(r.constraints.exists, new.constraints.exists), \or(r.constraints.attConstraints, new.constraints.attConstraints)>>>;
      mergedRows = true;
      break;
    }   
  }
  
  if (!mergedRows && constraintsForm != \false()) {
    current.indexedRows = current.indexedRows + <newPartialKeyTuple, <new.values, <new.constraints.exists, constraintsForm>>>;
  }
  
  return current;
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
  
  set[str] partialKey = lhs.partialKey & rhs.partialKey;
  
  IndexedRows lhsIndexed = index(lhs.rows, partialKey);
  IndexedRows rhsIndexed = index(rhs.rows, partialKey);
  
  IndexedRows result = lhsIndexed; 

  for (Tuple key <- rhsIndexed.indexedRows<0>, Row r <- rhsIndexed.indexedRows[key]) {
    result = addRow(result, r);
  }  
   
  return toRelation(result, lhs.heading); 
}
   
@memo
Relation intersect(Relation lhs, Relation rhs) {
  if (!unionCompatible(lhs,rhs)) {
    throw "INTERSECTION only works on union compatible relations";
  }

  if (lhs.rows == () || rhs.rows == ()) {
    return lhs;
  }

  set[str] partialKey = lhs.partialKey;
  set[str] openAttributes = lhs.heading<0> - partialKey;
  
  IndexedRows lhsIndexed = index(lhs.rows, partialKey);
  IndexedRows rhsIndexed = index(rhs.rows, partialKey);

  IndexedRows result = <partialKey, []>;
    
  for (Tuple key <- lhsIndexed.indexedRows<0>, key in rhsIndexed.indexedRows<0>, Row l <- lhsIndexed.indexedRows[key], Row r <- rhsIndexed.indexedRows[key]) {
    Formula tmpAttForm = \true();
    
    for (str att <- openAttributes) {
      tmpAttForm = \and(tmpAttForm, equal(l.values[att], r.values[att]));
    }
    
    result.indexedRows = result.indexedRows + <key, <l.values, <\and(l.constraints.exists, r.constraints.exists), tmpAttForm>>>;   
  } 
  
  return toRelation(result, lhs.heading);
}

@memo
Relation difference(Relation lhs, Relation rhs) {
  if (!unionCompatible(lhs,rhs)) {
    throw "DIFFERENCE only works on union compatible relations";
  }
  
  if (lhs.rows == () || rhs.rows == ()) {
    return lhs;
  }
  
  set[str] partialKey = lhs.partialKey & rhs.partialKey;
  set[str] openAttributes = lhs.heading<0> - partialKey;
  
  IndexedRows lhsIndexed = index(lhs.rows, partialKey);
  IndexedRows rhsIndexed = index(rhs.rows, partialKey);

  IndexedRows result = lhsIndexed;
    
  for (Tuple key <- lhsIndexed.indexedRows<0>, key in rhsIndexed.indexedRows<0>, Row l <- lhsIndexed.indexedRows[key], Row r <- rhsIndexed.indexedRows[key]) {
    Formula tmpAttForm = \true();

    for (str att <- openAttributes) {
      tmpAttForm = \and(tmpAttForm, equal(l.values[att], r.values[att]));
    }
    
    if (tmpAttForm == \true()) {
      // the rows are equal
      result.indexedRows = result.indexedRows - <key,l>;

      if (r.constraints.exists != \true()) {
        result.indexedRows = result.indexedRows + <key,<l.values, <\and(l.constraints.exists,\not(r.constraints.exists)),l.constraints.attConstraints>>>;
      }
    } else {
      // The rows are equal but have variables for their attributes. 
      result.indexedRows = result.indexedRows - <key,l> + <key,<l.values, <l.constraints.exists, implies(r.constraints.exists, not(tmpAttForm))>>>;
    }
  }
  
  return toRelation(result, lhs.heading);
}

@memo
Relation project(Relation relation, set[str] attributes) {
  Heading projectedHeading = (c : relation.heading[c] | str c <- relation.heading, c in attributes);
  
  if (size(projectedHeading) != size(attributes)) {
    throw "(Some of) the projected fields do not exists in the relation";
  }
  
  set[str] projectedPartialKey = relation.partialKey & getIdFields(projectedHeading);
  
  IndexedRows projectedRel = <projectedPartialKey, []>;
  
  for (Tuple tup <- relation.rows) {
    Tuple projectedTup = (att : tup[att] | str att <- tup, att in attributes);
    projectedRel = addRow(projectedRel, <projectedTup, relation.rows[tup]>);
  } 
  
  return toRelation(projectedRel, projectedHeading);
}

@memo
Relation rename(Relation relation, map[str,str] renamings) {
  // Check whether renamed attributes are part of this relation
  if (renamings<0> - relation.heading<0> != {}) {
    throw "Can not rename a non existing attribute";
  }
    
  Heading renamedHeading = ((old in renamings ? renamings[old] : old) : relation.heading[old] | str old <- relation.heading);
  if (size(renamedHeading) != size(relation.heading)) {
    // some attributes collapse together because of name clashes. This is not allowed
    throw "Renamed attributes overlap with existing attributenames";
  }  
  Rows renamedRows = ((((att in renamings) ? renamings[att] : att) : t[att] | str att <- t) : relation.rows[t] | Tuple t <- relation.rows);
  
  return <renamedHeading, renamedRows, {((f in renamings) ? renamings[f] : f) | str f <- relation.partialKey}>; 
}

@memo
Relation select(Relation relation, Formula (Tuple) criteria) {
  Rows result = (); 
  
  for (Tuple t <- relation.rows) {
    Formula attConstraints = \and(relation.rows[t].attConstraints, criteria(t)); 
    if (attConstraints != \false()) {
      result[t] = <relation.rows[t].exists, attConstraints>;
    }
  }
  
  return <relation.heading, result, relation.partialKey>;
}

@memo 
Relation aggregate(Relation relation, str bindTo, Domain bindToDomain, Term resultVar, Term (Row, Term) aggregateFunc, Term initialTerm) {
  Term aggregatedTerm = initialTerm;
  
  for (Tuple t <- relation.rows) {
    aggregatedTerm = aggregateFunc(<t, relation.rows[t]>, aggregatedTerm);
  }
  
  return <(bindTo:bindToDomain),((bindTo:resultVar):<\true(), equal(resultVar, aggregatedTerm)>), {}>; 
}

@memo
Relation product(Relation lhs, Relation rhs) {
  // Headings must be disjoint
  if (lhs.heading<0> & rhs.heading<0> != {}) {
    throw "PRODUCT only works on relations with disjoint attribute names";
  } 
  
  set[str] partialKey = lhs.partialKey + rhs.partialKey;
  
  IndexedRows result = <partialKey, []>;
  
  for (Tuple l <- lhs.rows, Tuple r <- rhs.rows) {
    Constraints joined = <\and(lhs.rows[l].exists, rhs.rows[r].exists), \and(lhs.rows[l].attConstraints, rhs.rows[r].attConstraints)>;
    if (isPresent(joined)) {
      result = addRow(result, <l+r, joined>);  
    }
  }
  
  return toRelation(result, lhs.heading + rhs.heading);
}

@memo
Relation naturalJoin(Relation lhs, Relation rhs) {
  // Must have attributes with the same name and domain
  set[str] joinAtts = (lhs.heading & rhs.heading)<0>;
  if (joinAtts == {}) {
    throw "No overlapping attributes to join";
  }
  
  set[str] joinPartialKey = lhs.partialKey+rhs.partialKey; 
  
  // Index on joining attributes
  IndexedRows indexedLhs = index(lhs.rows, joinAtts & joinPartialKey);
  IndexedRows indexedRhs = index(rhs.rows, joinAtts & joinPartialKey);

  bool joinOnKeysOnly = joinAtts & joinPartialKey == joinAtts;
  
  IndexedRows result = <joinPartialKey,[]>; 
  for (Tuple key <- indexedLhs.indexedRows<0>, key in indexedRhs.indexedRows<0>, Row lr <- indexedLhs.indexedRows[key], Row rr <- indexedRhs.indexedRows[key]) {
    Formula exists = \and(lr.constraints.exists,rr.constraints.exists);
    Formula attForm = \and(lr.constraints.attConstraints,rr.constraints.attConstraints);

    if (!joinOnKeysOnly) {
      for (str att <- joinAtts) {
        attForm = \and(attForm, equal(lr.values[att], rr.values[att]));
      }  
    }

    if (exists != \false() && attForm != \false()) {
      result = addRow(result, <lr.values+rr.values, <exists, attForm>>);
    }
  }
  
  return toRelation(result, lhs.heading + rhs.heading);
}

@memo
Relation transpose(Relation r, str first, str second) {
  if (size(r.heading) != 2 || r.heading[first] != id() || r.heading[second] != id()) {
    throw "TRANSPOSE only works for a binary relation with two id fields";
  }
 
  Rows result = ();
  for (Tuple t <- r.rows) {
    Tuple transposed = (first : t[second], second : t[first]);  
    result[transposed] = r.rows[t];
  } 
  
  return <r.heading, result, r.partialKey>;
}

@memo
Relation transitiveClosure(Relation r, str from, str to) {
  if (size(r.heading) != 2 || r.heading[from] != id() || r.heading[to] != id()) {
    throw "TRANSITIVE CLOSURE only works for a binary relation with two id fields";
  }
  
  int rows = size(r.rows); 

  Relation result = r;
  
  int i = 1;
  while(i < rows) {
    Relation tmp = rename(result, (from:to, to:"_tmp"));
    
    result = union(result, rename(project(naturalJoin(result, tmp),{from,"_tmp"}), ("_tmp":to)));
    
    i *= 2;
  } 
  
  return result; 
}

@memo
Relation reflexiveTransitiveClosure(Relation r, str from, str to, Relation iden) {
  if (size(r.heading) != 2 || r.heading[from] != id() || r.heading[to] != id()) {
    throw "REFLEXIVE TRANSITIVE CLOSURE only works for a binary relation with two id fields";
  }
  
  Relation result = union(transitiveClosure(r,from,to), iden);
  
  return result; 
} 

//@memo
//Relation ite(Formula \case, Relation \then, Relation \else) {
//  if (arity(then) != arity(\else)) {
//    throw "Arity of relation in THEN must be equal to the arity of the relation in ELSE for the ITE to work";
//  }
//
//  if (\case == \true()) {
//    return then;
//  } else if (\case == \false()) {
//    return \else;
//  } 
//  
//  Relation relResult = ();
//  
//  for (Index idx <- (then + \else)) {
//    Formula thenRel = ((idx in then) ? then[idx].relForm : \false());
//    Formula elseRel = ((idx in \else) ? \else[idx].relForm : \false()); 
//    
//    relResult[idx] = relOnly(ite(\case, thenRel, elseRel));
//  } 
//  
//  return relResult;
//}
