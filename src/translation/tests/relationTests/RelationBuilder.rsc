module translation::tests::relationTests::RelationBuilder

import smtlogic::Core;
import smtlogic::Ints;

import translation::AST;
import translation::Relation;

import Map;
import Set;
import List;

import IO;

alias Key = Tuple;

data RelationBuilder = rb(RelationBuilder (Tuple) t, RelationBuilder (Tuple) v, RelationBuilder (Tuple, Formula, Formula) f, Relation () build);

RelationBuilder create(str relName, Heading h) {
  map[str,int] pVarNames = ();
  str getVarName(Tuple t) {
    str base = toStr(relName, getKey(t));
    if (base notin pVarNames) {
      pVarNames[base] = 0;
      return "<base>";
    } else {
      pVarNames[base] += 1;
      return "<base>_<pVarNames[base]>";
    }
  }

  IndexedRows ir = index((), getIdFields(h));
   
  Row toRow(Tuple t, Formula present, Formula att) = <t, <present, att>>;  
   
  RelationBuilder truth(Tuple t) {
    ir = addRow(ir, toRow(t, \true(), \true()));    
    return rb(truth, variable, form, build);
  }

  RelationBuilder variable(Tuple t) {
    ir = addRow(ir, toRow(t, pvar(getVarName(t)), \true()));    
    return rb(truth, variable, form, build);
  }
  
  RelationBuilder form(Tuple t, Formula f, Formula att) {
    ir = addRow(ir, toRow(t, f, att));       
    return rb(truth, variable, form, build); 
  }
    
  Relation build() {
    return toRelation(ir, h); 
  }
  
  return rb(truth, variable, form, build);
}

Key getKey(Tuple t) = (f : t[f] | str f <- t, key(_) := t[f]);

str toStr(key(str k)) = k;
str toStr(str relName, Key key) = "<relName>_<intercalate("_", ["<toStr(key[k])>" | str k <- sortedKeys])>" when list[str] sortedKeys := sort(toList(key<0>)); 

test bool createEmptyRelation() {
  Relation r = create("testRel", ("id":id())).build();
  
  return isEmpty(r);
}

test bool twoDistinctRows() {
  Relation r = create("testRel", ("id":id())).t(("id":key("t1"))).t(("id":key("t2"))).build();
  
  return size(r.rows) == 2;
}

test bool noDuplicateRows_IdsOnly() {
  Relation r = create("testRel", ("id":id())).v(("id":key("t1"))).v(("id":key("t1"))).build();
  
  return size(r.rows) == 1 && r.rows[("id":key("t1"))].exists == \or({pvar("testRel_t1"),pvar("testRel_t1_1")});
}

data Domain = \int();

test bool emptyRelationWithExtraAttributes() {
  Relation r = create("testRel", ("id":id(), "num":\int())).build();
    
  return isEmpty(r);
}

test bool noDuplicateRows_IdsAndOtherAttributes() {
  Relation r = create("testRel", ("id":id(), "num":\int())).t(("id":key("p1"), "num":term(lit(\int(10))))).v(("id":key("p1"), "num":term(lit(\int(10))))).build();

  return size(r.rows) == 1 && r.rows[("id":key("p1"),"num":term(lit(\int(10))))].exists == \true();
}

test bool twoDistinctRows_IdsAndOtherAttributes() {
  Relation r = create("testRel", ("id":id(), "num":\int())).v(("id":key("p1"), "num":term(\var("n1",Sort::\int())))).v(("id":key("p1"), "num":term(\var("n2",Sort::\int())))).build();

  return size(r.rows) == 2;
}