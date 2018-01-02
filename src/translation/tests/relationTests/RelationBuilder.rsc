module translation::tests::relationTests::RelationBuilder

import smtlogic::Core;
import translation::AST;
import translation::Relation;

import Map;
import Set;
import List;

alias Row = map[str,Cell];

data RelationBuilder = rb(RelationBuilder (Row) t, RelationBuilder (Row, str) v, Relation () build);

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
    
    return rb(truth, variable, build);
  }

  RelationBuilder variable(Row r, str varName) {
    Key k = getKey(r);
    r -= k;
    relation.rows[k] = (k in relation.rows) ? relation.rows[k] + augment(k, r, pVar(varName)) : augment(k, r, pVar(varName));
    
    return rb(truth, variable, build);
  }
  
  Relation build() {
    return relation; 
  }
  
  return rb(truth, variable, build);
}

str toStr(key(str k)) = k;
str toStr(str relName, Key key) = "<relName>_<intercalate("_", ["<toStr(key[k])>" | str k <- sortedKeys])>" when list[str] sortedKeys := sort(toList(key<0>)); 
