module translation::tests::binderTests::TesterBase

import translation::Binder;
import logic::Propositional;

import IO;
import List;
 
RelationMatrix truth(list[str] vector) = (vector:relOnly(\true())); 
RelationMatrix truths(list[list[str]] vectors) = (() | it + truth(v) | v <- vectors);

RelationMatrix var(list[str] vector, str relName) = (vector:relOnly(var("<relName>_<relVar(vector)>")));
RelationMatrix vars(list[list[str]] vectors, str relName) = (() | it + var(v, relName) | v <- vectors);
 
str relVar(list[str] vector) = intercalate("_", vector);   