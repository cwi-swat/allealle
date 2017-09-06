module theories::tests::binderTests::TesterBase

import theories::Binder;
import theories::AST;

import logic::Propositional;

import IO;
import List;
 
RelationMatrix t(list[Atom] vector) = (vector:<\true(), ()>); 
RelationMatrix v(list[Atom] vector) = (vector:<var(relVar(vector)), ()>);
RelationMatrix v(list[Atom] vector, str baseName) = (vector:<var(relVar(baseName, vector)), ()>);
RelationMatrix f(list[Atom] vector) = (vector:<\false(), ()>);
RelationMatrix val(list[Atom] vector, Formula f) = (vector:<f, ()>);
 
void voidAdder(set[TheoryFormula] cons) {}    

private str relVar(list[Atom] vector) = intercalate("_", vector);   
private str relVar(str baseName, list[Atom] vector) = "<baseName>_<intercalate("_", vector)>";  