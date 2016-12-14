module orig::AST

alias Atom = str;

data Problem = problem(Universe uni, list[RelationalBound] bounds, list[Formula] formulas);

data Universe = universe(list[Atom] atoms);

data RelationalBound = relationalBound(str relName, int arity, list[Tuple] lowerBounds, list[Tuple] upperBounds);

data Tuple = \tuple(list[Atom] atoms);	
  
data Formula
	= empty(Expr expr)
	| atMostOne(Expr expr)
	| exactlyOne(Expr expr)
	| nonEmpty(Expr expr)
	| subset(Expr lhsExpr, Expr rhsExpr)
	| equal(Expr lhsExpr, Expr rhsExpr)
	| negation(Formula form)
	| conjunction(Formula lhsForm, Formula rhsForm)
	| disjunction(Formula lhsForm, Formula rhsForm)
	| implication(Formula lhsForm, Formula rhsForm)
	| equality(Formula lhsForm, Formula rhsForm)
	| universal(list[VarDeclaration] decls, Formula form)
	| existential(list[VarDeclaration] decls, Formula form) 
	; 

data Expr
	= variable(str name)
	| transpose(Expr expr)
	| closure(Expr expr)
	| reflexClosure(Expr expr)
	| union(Expr lhs, Expr rhs) 
	| intersection(Expr lhs, Expr rhs)
	| difference(Expr lhs, Expr rhs)
	| \join(Expr lhs, Expr rhs)
	| accessorJoin(Expr col, Expr select)
	| product(Expr lhs, Expr rhs)
	| ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr)
	| comprehension(list[VarDeclaration] decls, Formula form)
	;

data VarDeclaration = varDecl(str name, Expr binding);