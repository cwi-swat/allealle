module logic::Integer

data Formula
	= \int(int i)
	| intVar(str name)
	| lt(Formula lhs, Formula rhs)
	| lte(Formula lhs, Formula rhs)
	| gt(Formula lhs, Formula rhs)
	| gte(Formula lhs, Formula rhs)
	| equal(Formula lhs, Formula rhs)
	| addition(set[Formula] formulas)
	| substraction(set[Formula] formulas)
	| multiplication(set[Formula] formulas)
	| division(set[Formula] formulas)
	;
	
Formula multiplication({i:\int(_)}) = i;
Formula multiplication(Formula lhs, Formula rhs) = multiplication({lhs, rhs});
Formula multiplication({\int(int a), \int(int b), *Formula rest}) = multiplication({\int(a*b), *rest});