module theories::relational::tests::binderTests::TesterBase

import theories::relational::Binder;
import theories::relational::AST;

import logic::Propositional;

import IO;
import List;

private Binding t(list[Atom] vector) = (<relTheory(),vector>:\true()); 
private Binding v(list[Atom] vector) = (<relTheory(),vector>:var(relVar(vector)));
private Binding f(list[Atom] vector) = (<relTheory(),vector>:\false());
private Binding val(list[Atom] vector, Formula f) = (<relTheory(),vector>:f);

private str relVar(list[Atom] vector) = intercalate("_", vector);  