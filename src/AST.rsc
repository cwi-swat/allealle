module AST

alias Atom = str;

data Theory;

data Problem = problem(Universe uni, list[RelationalBound] bounds, list[Formula] constraints);

data RelationalBound 
  = relationalBound(str relName, int arity, list[Tuple] lowerBounds, list[Tuple] upperBounds)
  | relationalBoundWithTheory(str relName, Theory theory, int arity, list[Tuple] lowerBounds, list[Tuple] upperBounds)
  ;

data Tuple = \tuple(list[Atom] atoms);  

data Universe = universe(list[Atom] atoms);

data Formula;
data Expr;