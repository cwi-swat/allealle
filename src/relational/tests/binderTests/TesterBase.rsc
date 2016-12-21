module relational::tests::binderTests::TesterBase

import relational::Binder;
import relational::AST;

import logic::Propositional;

import IO;

private Binding t(Atom x) = (<relational(),[x]>:\true()); 
private Binding t(Atom x, Atom y) = (<relational(),[x,y]>:\true());
private Binding t(Atom x, Atom y, Atom z) = (<relational(),[x,y,z]>:\true());

private Binding v(Atom x) = (<relational(),[x]>:var(x));
private Binding v(Atom x, Atom y) = (<relational(),[x,y]>:var("<x>_<y>"));
private Binding v(Atom x, Atom y, Atom z) = (<relational(),[x,y,z]>:var("<x>_<y>"));

private Binding f(Atom x) = (<relational(),[x]>:\false());
private Binding f(Atom x, Atom y) = (<relational(),[x,y]>:\false());
private Binding f(Atom x, Atom y, Atom z) = (<relational(),[x,y,z]>:\false());

private Binding val(Atom x, Formula f) = (<relational(),[x]>:f);
private Binding val(Atom x, Atom y, Formula f) = (<relational(),[x,y]>:f); 
private Binding val(Atom x, Atom y, Atom z, Formula f) = (<relational(),[x,y,z]>:f); 