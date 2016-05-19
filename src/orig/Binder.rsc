module orig::Binder

import logic::Propositional;
import orig::AST;

import List;
import Relation;
import Map;
import Set;
import IO;

// index is a tuple of different arity depending on type of relation (unary, binary) 
alias Index = value;
alias Binding = map[Index, Formula]; 

Binding createSingletonBinding(Binding orig, Index x) = (y:val | Index y <- orig, Formula val := ((y == x) ? \true() : \false()));

int arity(Binding b) = 1 when /<Atom _> := domain(b);
int arity(Binding b) = 2 when /<Atom _, Atom _> := domain(b);
default int arity(Binding b) { throw "Relations with an arity greater then 2 are not allowed";}

bool sameArity(Binding lhs, Binding rhs) = arity(lhs) == arity(rhs); 

Binding transpose(Binding m) = transpose(arity(m), m);
Binding transpose(1, Binding m) = m;
Binding transpose(2, Binding m) =(() | it + (<b,a>:m[idx]) | Index idx:<Atom a, Atom b> <- m);
default Binding transpose(int arity, Binding _) { throw "Unable to transpose a relation of arity <arity>";}

int si(Binding m) = size(m) when arity(m) == 1;
int si(Binding m) = size(m) when arity(m) == 2;	
default int si(Binding m) { throw "Unable to get the size of a relation with an arity greater then 2"; } 
	
Binding square(Binding m, int s) = m when size(m) <= s;
Binding square(Binding m, int s) = or(n, \join(n, n)) when Binding n := square(m, s * 2); 
default Binding square(Binding _, int s) { throw "Unable to square a binding with a size of <s>"; }

Binding identity(Binding orig) = identity(arity(orig), orig);
Binding identity(2, Binding orig) = (idx:val | Index idx:<Atom a, Atom b> <- orig, Formula val := (a == b ? \true() : \false()));
default Binding identity(int arity, Binding orig) { throw "Unable to construct a identity binding for a relations of arity <arity>";}	
	
Binding or(Binding lhs, Binding rhs) = (x:\or(lhs[x],rhs[x]) | Index x <- lhs) when sameArity(lhs, rhs);
default Binding or(Binding _, Binding _) { throw "Unable to perform disjunction of bindings with different arity"; }

Binding and(Binding lhs, Binding rhs) = (x:\and(lhs[x],rhs[x]) | Index x <- lhs) when sameArity(lhs, rhs);
default Binding and(Binding _, Binding _) { throw "Unable to perform conjunction of bindings with different arity"; }

Binding not(Binding orig) = (idx:not(orig[idx]) | Index idx <- orig);

Binding product(Binding lhs, Binding rhs) = product(arity(lhs), arity(rhs), lhs, rhs);
Binding product(1, 1, Binding lhs, Binding rhs) = (<a,b>:\and(lhs[x],rhs[y]) | x:<Atom a> <- lhs, y:<Atom b> <- rhs);
Binding product(2, 2, Binding lhs, Binding rhs)
	= (<aa,ab,ba,bb>:\and(lhs[x],rhs[y]) | <Atom aa, _> <- lhs, Index x:<aa, Atom ab> <- lhs, <Atom ba, _> <- rhs, Index y:<ba, Atom bb> <- rhs);
default Binding product(int arityLhs, int arityRhs, Binding _, Binding _) { throw "Cannot create product between two relations with arity <arityLhs> and <arityRhs>"; }

Binding \join(Binding lhs, Binding rhs) = \join(arity(lhs), arity(rhs), lhs, rhs);	
Binding \join(1, 1, Binding lhs, Binding rhs) { throw "Cannot join two relations of arity 1";}	
Binding \join(1, 2, Binding lhs, Binding rhs)	
	= (<row>:\or({\and({lhs[<x>], rhs[y]}) | <Atom x> <- lhs, Index y:<Atom x, row> <- rhs}) | <Atom row> <- lhs);

Binding \join(2, 1, Binding lhs, Binding rhs)  
	= (<row>:\or({\and({lhs[y], rhs[<x>]}) | Index y:<row, Atom x> <- lhs}) | <Atom row, _> <- lhs);
			
Binding \join(2, 2, Binding lhs, Binding rhs) 
	= (idx:(\false() | \or({it, \and({lhs[<row,x>], rhs[<x,col>]})}) | <row, Atom x> <- lhs) | Index idx:<Atom row, Atom col> <- lhs);
		
default Binding \join(int arityLhs, int arityRhs, Binding lhs, Binding rhs) { throw "Unsupported join of relations with arity <arityLhs> and <arityRhs>";}
