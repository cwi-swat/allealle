module logic::Integer

extend logic::Propositional;

import IO;

data Sort
  = \int()
  ;

data Formula
	= lt(Expr lhs, Expr rhs)
	| lte(Expr lhs, Expr rhs)
	| gt(Expr lhs, Expr rhs)
	| gte(Expr lhs, Expr rhs)
	;

data Expr
  = \int(int i)
  | neg(Expr e)
  | abs(Expr e)
  | addition(list[Expr] terms)
  | multiplication(list[Expr] terms)
  | division(Expr lhs, Expr rhs)
  | modulo(Expr lhs, Expr rhs) 
  ;

data Command
  = minimize(Formula f)
  | maximize(Formula f)
  ;
	
Sort sortOfLit(\int(_)	) = \int();
	
Expr addition(\int(0), Expr rhs) = rhs;
Expr addition(Expr lhs, \int(0)) = lhs;
Expr addition(\int(a), \int(b)) = \int(a+b);	
Expr addition(addition(list[Expr] l), Expr r) = addition([*l, r]);
Expr addition(Expr l, addition(list[Expr] r)) = addition([l, *r]);
default Expr addition(Expr lhs, Expr rhs) = addition([lhs,rhs]);

Expr substraction(\int(0), Expr rhs) = rhs;
Expr substraction(Expr lhs, \int(0)) = lhs;
Expr substraction(\int(a), \int(b)) = \int(a-b);
default Expr substraction(Expr lhs, Expr rhs) = addition([lhs, neg(rhs)]);

Expr multiplication(\int(0), Expr rhs) = \int(0);
Expr multiplication(Expr lhs, \int(0)) = \int(0);
Expr multiplication(\int(1), Expr rhs) = rhs;
Expr multiplication(Expr lhs, \int(1)) = lhs;
Expr multiplication(\int(a),\int(b)) = \int(a*b);
Expr multiplication(multiplication(list[Expr] l), Expr r) = multiplication([*l, r]);
Expr multiplication(Expr l, multiplication(list[Expr] r)) = multiplication([l, *r]);
default Expr multiplication(Expr lhs, Expr rhs) = multiplication([lhs,rhs]);

Expr division(\int(x), \int(y)) = \int(x/y);
Expr modulo(\int(x),\int(y)) = \int(x%y); 

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