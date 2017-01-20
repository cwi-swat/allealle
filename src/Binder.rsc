module Binder

import AST;
import logic::Boolean;

import List;

alias Index = tuple[Theory theory, list[Atom] vector];
alias Binding = map[Index, Formula];

alias LookupKey = str;

alias Environment = map[LookupKey, Binding];

@memo
int sizeOfUniverse(Universe u) = size(u.atoms);

@memo
private int arity(Binding b) {
  for (Index idx <- b) {
    return size(idx.vector);
  }
  
  return 0;
}

@memo
private bool sameArity(Binding lhs, Binding rhs) = arity(lhs) == arity(rhs); 
 

