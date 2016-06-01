module orig::tests::binderTests::BinderTesterBase

import orig::Binder;
import orig::AST;

import logic::Propositional;

import IO;

private Binding t(Atom x) = (<x, relTheory()>:\true()); 
private Binding t(Atom x, Atom y) = (<x,y, relTheory()>:\true());

private Binding v(Atom x) = (<x, relTheory()>:var(x));
private Binding v(Atom x, Atom y) = (<x,y, relTheory()>:var("<x>_<y>"));

private Binding f(Atom x) = (<x, relTheory()>:\false());
private Binding f(Atom x, Atom y) = (<x,y, relTheory()>:\false());

private Binding val(Atom x, Formula f) = (<x, relTheory()>:f);
private Binding val(Atom x, Atom y, Formula f) = (<x,y, relTheory()>:f);