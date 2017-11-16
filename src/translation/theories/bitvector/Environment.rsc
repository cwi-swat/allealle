module translation::theories::bitvector::Environment

extend translation::Environment;

import translation::theories::bitvector::AST;
import logic::Integer; 
 
Formula createAttribute(Index idx, str name, \int(), hole()) = toIntVar(idx, name);  
Formula createAttribute(Index idx, str name, \int(), lit(posInt(int i))) = \int(i);  
Formula createAttribute(Index idx, str name, \int(), lit(negInt(int i))) = neg(\int(i));  
