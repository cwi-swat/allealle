module extended::Binder

extend orig::Binder;

import logic::Integer;

Binding multiply(Binding lhs, Binding rhs) 
	= (idx:multiplication(lhs[idx], rhs[idx]) | Index idx:<Atom a> <- lhs, idx in rhs, Formula lhsVal := (lhs[idx] == \true()) ? var(")
	when sameArity(lhs, rhs);
	
default Binding multiply(Binding lhs, Binding rhs) { throw "Can not multiply two relations with arity <arity(lhs)> and <arity(rhs)>"; }

