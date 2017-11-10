module translation::theories::integer::Environment

extend translation::Environment;

import translation::theories::integer::Binder;
import translation::theories::integer::AST;
import logic::Integer; 
 
Formula createAttribute(Index idx, str name, \int(), hole()) = toIntVar(idx, name);  
Formula createAttribute(Index idx, str name, \int(), lit(posInt(int i))) = \int(i);  
Formula createAttribute(Index idx, str name, \int(), lit(negInt(int i))) = neg(\int(i));  
