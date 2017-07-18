module logic::Integer

extend logic::Propositional;

import IO;

data Formula
	= \int(int i)
	| intVar(str name)
	| neg(Formula f)
	| lt(Formula lhs, Formula rhs)
	| lte(Formula lhs, Formula rhs)
	| gt(Formula lhs, Formula rhs)
	| gte(Formula lhs, Formula rhs)
	| equal(Formula lhs, Formula rhs)
	| inequal(Formula lhs, Formula rhs)
	| addition(list[Formula] forms)
	| multiplication(list[Formula] forms)
	| division(Formula lhs, Formula rhs)
	| modulo(Formula lhs, Formula rhs) 
	;

data Command
  = minimize(Formula f)
  | maximize(Formula f)
  ;
	
Formula addition(\int(0), Formula rhs) = rhs;
Formula addition(Formula lhs, \int(0)) = lhs;	
Formula addition(addition(list[Formula] l), Formula r) = addition([*l, r]);
Formula addition(Formula l, addition(list[Formula] r)) = addition([l, *r]);
default Formula addition(Formula lhs, Formula rhs) = addition([lhs,rhs]);

Formula substraction(\int(0), Formula rhs) = rhs;
Formula substraction(Formula lhs, \int(0)) = lhs;
default Formula substraction(Formula lhs, Formula rhs) = addition([lhs, neg(rhs)]);

Formula multiplication(\int(0), Formula rhs) = \int(0);
Formula multiplication(Formula lhs, \int(0)) = \int(0);
Formula multiplication(\int(1), Formula rhs) = rhs;
Formula multiplication(Formula lhs, \int(1)) = lhs;
default Formula multiplication(Formula lhs, Formula rhs) = multiplication([lhs,rhs]);

Formula addition(\int(x), \int(y)) = \int(x+y);
Formula multiplication(\int(x), \int(y)) = \int(x*y);

Formula modulo(\int(x),\int(y)) = \int(x%y); 

Formula lt(\int(x),\int(y)) = \false() when x >= y;
Formula lt(\int(x),\int(y)) = \true() when x < y;

Formula lte(\int(x),\int(y)) = \false() when x > y;
Formula lte(\int(x),\int(y)) = \true() when x <= y;

Formula equal(\int(x),\int(y)) = \false() when x != y;
Formula equal(\int(x),\int(x)) = \true();

Formula gt(\int(x),\int(y)) = \false() when x <= y;
Formula gt(\int(x),\int(y)) = \true() when x > y;

Formula gte(\int(x),\int(y)) = \false() when x < y;
Formula gte(\int(x),\int(y)) = \true() when x >= y;
