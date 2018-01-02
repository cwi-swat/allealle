module translation::tests::relationTests::RelationBuilder

import smtlogic::Core;
import translation::AST;
import translation::Relation;

import Map;
import Set;
import List;

alias Row = map[str,Cell];

data RelationBuilder = rb(RelationBuilder (Row) t, RelationBuilder (Row) v, RelationBuilder (Row, Formula) f, Relation () build);

RelationBuilder create(str relName, Header h) {
  Relation relation = <h,()>;
  
  Key getKey(Row r) {
    Key rowKey = ();
    
    set[str] keyFromHeader = getIdFieldsFromHeader(relation.header);
    for (str key <- keyFromHeader) {
      if (key notin r) {
        throw "Supplied row \'<r>\' does not contain required key field \'<key>\'";
      }
      
      rowKey[key] = r[key];
    }
    
    return rowKey;  
  }
  
  Attributes augment(Key k, Row r, Formula f = \true()) { 
     r += formulaCol() notin r ? (formulaCol():formula(f)) : (); 
     r += constraintsCol() notin r ? (constraintsCol():formula(\true())) : ();
      
     return r;
  }
   
  RelationBuilder truth(Row r) {
    Key k = getKey(r);
    r -= k;
    relation.rows[k] = (k in relation.rows) ? relation.rows[k] + augment(k, r) : augment(k, r);
    
    return rb(truth, variable, form, build);
  }

  RelationBuilder variable(Row r) {
    Key k = getKey(r);
    r -= k;
    relation.rows[k] = (k in relation.rows) ? relation.rows[k] + augment(k, r, f = pvar(toStr(relName, k))) : augment(k, r, f = pvar(toStr(relName, k)));
    
    return rb(truth, variable, form, build);
  }
  
  RelationBuilder form(Row r, Formula f) {
    Key k = getKey(r);
    r -= k;
    relation.rows[k] = (k in relation.rows) ? relation.rows[k] + augment(k, r, f=f) : augment(k, r, f=f);
    
    return rb(truth, variable, form, build);
  }
    
  Relation build() {
    return relation; 
  }
  
  return rb(truth, variable, form, build);
}

str toStr(key(str k)) = k;
str toStr(str relName, Key key) = "<relName>_<intercalate("_", ["<toStr(key[k])>" | str k <- sortedKeys])>" when list[str] sortedKeys := sort(toList(key<0>)); 
