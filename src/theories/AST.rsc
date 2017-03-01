module theories::AST

data Problem = problem(Universe uni, list[RelationalBound] bounds, list[AlleFormula] constraints);

data Universe = universe(list[Atom] atoms);

data RelationalBound 
  = relationalBound(str relName, int arity, list[Tuple] lowerBounds, list[Tuple] upperBounds)
  | relationalBoundWithTheory(str relName, Theory theory, int arity, list[Tuple] lowerBounds, list[Tuple] upperBounds)
  ;

data Tuple = \tuple(list[Atom] atoms);  

alias Atom = str;

data Theory;

data AlleFormula;
data Expr;