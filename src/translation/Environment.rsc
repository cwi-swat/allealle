module translation::Environment

import logic::Propositional;

import translation::AST;
import translation::Binder;

import List;

alias Environment = tuple[map[str, RelationMatrix] relations, map[Index, map[str, Formula]] attributes, list[Id] idDomain]; 

Environment createInitialEnvironment(Problem p) {
  list[Id] idDomain = extractIdDomain(p);
 
  map[str, RelationMatrix] relations = (r.name:createRelationMatrix(r) | Relation r <- p.relations);
  map[Index, map[str, Formula]] attributes = (() | createAttributeLookup(r, it) | r:relationWithAttributes(str name, int arityOfIds, list[AttributeHeader] headers, RelationalBound bounds) <- p.relations); 
   
  return <relations, attributes, idDomain>;
}   
                      
list[Id] extractIdDomain(Problem p) {
  list[Tuple] getTuples(exact(list[Tuple] tuples)) = tuples;
  list[Tuple] getTuples(atMost(list[Tuple] upper)) = upper;
  list[Tuple] getTuples(atLeastAtMost(_, list[Tuple] upper)) = upper;
  
  return dup([id | Relation r <- p.relations, Tuple t <- convertTuples(getTuples(r.bounds)), id(Id id) <- t.values]);   
}                      
                                                                                                                                                    
RelationMatrix createRelationMatrix(Relation r) {
  @memo
  str idxToStr(Index idx) = intercalate("_", idx);
  
  tuple[list[Index] lb, list[Index] ub] bounds = getBounds(r.arityOfIds, r.bounds);
  
  RelationMatrix relResult = (); 
    
  for (Index idx <- bounds.lb) {
    relResult += (idx : relOnly(\true()));
  }

  for (Index idx <- bounds.ub, idx notin bounds.lb) {
    relResult += (idx : relOnly(var("<r.name>_<idxToStr(idx)>")));
  }

  return relResult;
} 

@memo
list[Tuple] convertTuples(list[Tuple] tuples) = [*convertTuple(t) | Tuple t <- tuples];
 
list[Tuple] convertTuple(t:tup(list[Value] _)) = [t]; 
list[Tuple] convertTuple(range(list[RangedValue] from, list[RangedValue] to)) {
  if (size(from) != size(to)) {
    throw "Unable to build tuples from ranges, arity of from and to do not match";
  } 
  
  list[list[Id]] newTupleIds = [];
  list[Value] templates = [];
  for (int i <- [0..size(from)]) {
    if (id(str prefixFrom, int numFrom) := from[i], id(prefixTo, int numTo) := to[i]) {
      if (prefixFrom != prefixTo) {
        throw "Can not change the alphanummeric prefix in a ranged tuple for an id in the same column";
      } 
      
      newTupleIds += [["<prefixFrom><n>" | int n <- [numFrom..numTo+1]]];
    } else if (id(_,_) !:= from[i], from[i] == to[i]) {
      templates += convert(from[i]);
    } else {
      throw "Can not create tuples from declared range. Template attribute definitions do not match";
    }
  }
    
  return buildTuplesFromRange(newTupleIds, [], templates);
} 
  
list[Tuple] buildTuplesFromRange([], list[Value] currentIdx, list[Value] templates) = [tup([*currentIdx,*templates])];
list[Tuple] buildTuplesFromRange([list[Id] hd, *list[Id] tl], list[Value] currentIdx, list[Value] templates) = [*buildTuplesFromRange(tl, currentIdx + id(i), templates) | Id i <- hd];

Value convert(templateLit(Literal l)) = lit(l);
Value convert(templateHole()) = hole();
default Value convert(RangedValue v) { throw "Unable to convert \'v\' to a Value"; }

tuple[list[Index], list[Index]] getBounds(int arity, exact(list[Tuple] tuples)) = <b,b> when list[Index] b := getIndices(arity, convertTuples(tuples));
tuple[list[Index], list[Index]] getBounds(int arity, atMost(list[Tuple] upper)) = <[], ub> when list[Index] ub := getIndices(arity, convertTuples(upper));
tuple[list[Index], list[Index]] getBounds(int arity, atLeastAtMost(list[Tuple] lower, list[Tuple] upper)) = <lb,ub> when list[Index] lb := getIndices(arity, convertTuples(lower)), list[Index] ub := getIndices(arity, convertTuples(upper));

@memo      
private list[Index] getIndices(int arity, list[Tuple] tuples) {
  list[Index] indices = [];
  for (Tuple t <- tuples) {
     Index idx = [id | id(Id id) <- t.values];
     
     if (size(idx) != arity) {
      throw "Arity definition of id field and nr of ids in tuples do not match";
     }
     
     indices += [idx];
  }
  
  return indices;
}

map[Index, map[str, Formula]] createAttributeLookup(relationWithAttributes(str _, int arityOfIds, list[AttributeHeader] headers, RelationalBound bounds), map[Index, map[str, Formula]] currentLookup) {
  map[Index, map[str, Formula]] partial = createPartialAttributeLookup(arityOfIds, headers, bounds);
  
  for (Index idx <- partial) {
    if (idx in currentLookup) {
      currentLookup[idx] += partial[idx];
    } else {
      currentLookup[idx] = partial[idx];
    }
  }     
  
  return currentLookup;
} 

map[Index, map[str, Formula]] createPartialAttributeLookup(int arityOfIds, list[AttributeHeader] headers, exact(list[Tuple] tuples)) = createPartialAttributeLookup(arityOfIds, headers, convertTuples(tuples));
map[Index, map[str, Formula]] createPartialAttributeLookup(int arityOfIds, list[AttributeHeader] headers, atMost(list[Tuple] upper)) = createPartialAttributeLookup(arityOfIds, headers, convertTuples(upper));
map[Index, map[str, Formula]] createPartialAttributeLookup(int arityOfIds, list[AttributeHeader] headers, atLeastAtMost(list[Tuple] _, list[Tuple] upper)) = createPartialAttributeLookup(arityOfIds, headers, convertTuples(upper));

private map[Index, map[str, Formula]] createPartialAttributeLookup(int arityOfIds, list[AttributeHeader] headers, list[Tuple] tuples) {
  map[Index, map[str, Formula]] result = ();
  
  for (Tuple t <- tuples) {
    Index idx = [id | id(Id id) <- t.values];
    if (arityOfIds + size(headers) != size(t.values)) {
      throw "Total arity of relation and size of the defined tuples differ";
    }

    map[str, Formula] attributes = ();
        
    for (int i <- [0..size(headers)], AttributeHeader h := headers[i], Value v := t.values[arityOfIds + i]) {
      attributes[h.name] = createAttribute(idx, h.name, h.dom, v);  
    }
    
    result[idx] = attributes;  
  }
  
  return result;
}      
       
default Formula createAttribute(Index idx, str name, Domain d, Value v) { throw "No attribute creator found for domain \'<d>\' with value \'<v>\'"; } 
