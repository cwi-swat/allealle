module logic::Integer

extend logic::Boolean;

data Formula
	= \int(int i)
	| intVar(str name)
	| neg(Formula f)
	| lt(Formula lhs, Formula rhs)
	| lte(Formula lhs, Formula rhs)
	| gt(Formula lhs, Formula rhs)
	| gte(Formula lhs, Formula rhs)
	| equal(Formula lhs, Formula rhs)
	| addition(Formula lhs, Formula rhs)
	| substraction(Formula lhs, Formula rhs)
	| multiplication(Formula lhs, Formula rhs)
	| division(Formula lhs, Formula rhss)
	;
	

