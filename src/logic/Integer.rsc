module logic::Integer

extend logic::Propositional;

data Formula
	= \int(int i)
	| intVar(str name)
	| neg(Formula f)
	| lt(Formula lhs, Formula rhs)
	| lte(Formula lhs, Formula rhs)
	| gt(Formula lhs, Formula rhs)
	| gte(Formula lhs, Formula rhs)
	| equal(Formula lhs, Formula rhs)
	| addition(set[Formula] forms)
	| multiplication(set[Formula] forms)
	| division(Formula lhs, Formula rhss)
	;
	
Formula addition(Formula lhs, Formula rhs) = addition({lhs,rhs});
Formula substraction(Formula lhs, Formula rhs) = addition({lhs, neg(rhs)});
Formula multiplication(Formula lhs, Formula rhs) = multiplication({lhs,rhs});

Formula addition(\int(x), \int(y)) = \int(x+y);
Formula multiplication(\int(x), \int(y)) = \int(x*y);

Formula lt(\int(x),\int(y)) = \false() when x >= y;
Formula lt(\int(x),\int(y)) = \true() when x < y;

Formula lte(\int(x),\int(y)) = \false() when x > y;
Formula lte(\int(x),\int(y)) = \false() when x <= y;

Formula equal(\int(x),\int(y)) = \false() when x != y;
Formula equal(\int(x),\int(x)) = \true();

Formula gt(\int(x),\int(y)) = \false() when x <= y;
Formula gt(\int(x),\int(y)) = \false() when x > y;

Formula gte(\int(x),\int(y)) = \false() when x < y;
Formula gte(\int(x),\int(y)) = \false() when x >= y;
