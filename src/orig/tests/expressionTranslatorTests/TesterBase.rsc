module orig::tests::expressionTranslatorTests::TesterBase

import orig::ExpressionTranslator;
import orig::AST;

import logic::Propositional;

import IO;

private Binding t(Atom x) = ([x]:\true()); 
private Binding t(Atom x, Atom y) = ([x,y]:\true());
private Binding t(Atom x, Atom y, Atom z) = ([x,y,z]:\true());

private Binding v(Atom x) = ([x]:var(x));
private Binding v(Atom x, Atom y) = ([x,y]:var("<x>_<y>"));
private Binding v(Atom x, Atom y, Atom z) = ([x,y,z]:var("<x>_<y>"));

private Binding f(Atom x) = ([x]:\false());
private Binding f(Atom x, Atom y) = ([x,y]:\false());
private Binding f(Atom x, Atom y, Atom z) = ([x,y,z]:\false());

private Binding val(Atom x, Formula f) = ([x]:f);
private Binding val(Atom x, Atom y, Formula f) = ([x,y]:f); 
private Binding val(Atom x, Atom y, Atom z, Formula f) = ([x,y,z]:f); 