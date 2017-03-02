module theories::relational::tests::binderTests::TesterBase

import theories::relational::Binder;
import theories::relational::AST;

import logic::Propositional;

import IO;

private Binding t(Atom x) = (<relTheory(),[x]>:\true()); 
private Binding t(Atom x, Atom y) = (<relTheory(),[x,y]>:\true());
private Binding t(Atom x, Atom y, Atom z) = (<relTheory(),[x,y,z]>:\true());

private Binding v(Atom x) = (<relTheory(),[x]>:var(x));
private Binding v(Atom x, Atom y) = (<relTheory(),[x,y]>:var("<x>_<y>"));
private Binding v(Atom x, Atom y, Atom z) = (<relTheory(),[x,y,z]>:var("<x>_<y>"));

private Binding f(Atom x) = (<relTheory(),[x]>:\false());
private Binding f(Atom x, Atom y) = (<relTheory(),[x,y]>:\false());
private Binding f(Atom x, Atom y, Atom z) = (<relTheory(),[x,y,z]>:\false());

private Binding val(Atom x, Formula f) = (<relTheory(),[x]>:f);
private Binding val(Atom x, Atom y, Formula f) = (<relTheory(),[x,y]>:f); 
private Binding val(Atom x, Atom y, Atom z, Formula f) = (<relTheory(),[x,y,z]>:f); 