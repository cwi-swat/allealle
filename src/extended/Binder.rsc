module extended::Binder

extend orig::Binder;

import logic::Integer;

data Theory = intTheory();

Binding multiply(Binding lhs, Binding rhs) 
	= (idx:multiplication(lhs[idx], rhs[idx]) | Index idx:<Atom a, intTheory()> <- lhs, idx in rhs)
	when arity(lhs) == 1 && arity(rhs) == 1;
		
default Binding multiply(Binding lhs, Binding rhs) { throw "Can not multiply two relations with arity <arity(lhs)> and <arity(rhs)>"; }
	
Binding divide(Binding lhs, Binding rhs) 
	= (idx:division(lhs[idx], rhs[idx]) | Index idx:<Atom a, intTheory()> <- lhs, idx in rhs)
	when arity(lhs) == 1 && arity(rhs) == 1;

default Binding divide(Binding lhs, Binding rhs) { throw "Can not divide two relations with arity <arity(lhs)> and <arity(rhs)>"; }
	
Binding add(Binding lhs, Binding rhs) 
	= (idx:addition(lhs[idx], rhs[idx]) | Index idx:<Atom a, intTheory()> <- lhs, idx in rhs)
	when arity(lhs) == 1 && arity(rhs) == 1;

default Binding add(Binding lhs, Binding rhs) { throw "Can not add two relations with arity <arity(lhs)> and <arity(rhs)>"; }

Binding substract(Binding lhs, Binding rhs) 
	= (idx:substraction(lhs[idx], rhs[idx]) | Index idx:<Atom a, intTheory()> <- lhs, idx in rhs)
	when arity(lhs) == 1 && arity(rhs) == 1;

default Binding substract(Binding lhs, Binding rhs) { throw "Can not substract two relations with arity <arity(lhs)> and <arity(rhs)>"; }
	