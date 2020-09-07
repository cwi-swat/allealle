module translation::SymmetryBreaker

import translation::AST;
import translation::Environment;
import translation::Relation;

import smtlogic::Core;

import IO;
import Map;
import Set;

Formula buildSymmetryBreakingPredicates(Problem p, Environment env) {
  bool hasIdAtt(Heading h) = id() in range(h);
  str getIdAtt(Heading h) {
    for (att <- h, h[att] == id()) {
      return att;
    }
    
    throw "Heading has no Id attributes";
  }
    
  set[set[Id]] partition(Relation r, set[set[Id]] partitions) {
    if (!hasIdAtt(r.heading)) {
      return partitions;
    }
    
    // select one id attribute from the relation as starting point
    str att = getIdAtt(r.heading);  
    // create a set of ids containing ids from attribute
    set[Id] first = {i | Tuple t <- r.rows, lit(id(str i)) := t[att]};
    
    for (set[Id] s <- partitions, s - first != {}, (s & first) != {}) {
      partitions -= {s};
      partitions += {s & first} + {(s - first)};
    }
    
    //if (arity(r) > 1) {
    //  set[Id] new = {};
    //  
    //  for (s <- partitions, s & first != {}) {
    //    partitions -= {s};
    //    
    //    while (s != {}) {
    //      x = getOneFrom(s);
    //    }
    //  }
    //}
    
    return partitions;
  }
  
  Formula buildPredicate(Relation r, set[set[Id]] partitions) {
    if (!hasIdAtt(r.heading) || arity(r) > 1) {
      return \true();
    }
    
    
  }
  
  list[Id] ids = extractIdDomain(p);
  
  set[set[Id]] partitions = ({{id | id <- ids}} | partition(env.relations[r], it) | str r <- env.relations);
  
  iprintln(partitions);
  
  set[Formula] clauses = {buildPredicate(env.relations[r],partitions) | str r <- env.relations};
    
  return \and(clauses);
}