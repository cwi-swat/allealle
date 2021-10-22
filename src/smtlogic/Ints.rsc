module smtlogic::Ints

import smtlogic::Core;

import IO;

data Sort
  = \int()
  ;

data Formula
	= lt(Term tLhs, Term tRhs)
	| lte(Term tLhs, Term tRhs)
	| gt(Term tLhs, Term tRhs)
	| gte(Term tLhs, Term tRhs)
	;

data Term
  = neg(Term e)
  | abs(Term e)
  | exp(Term base, Term expo)
  | addition(list[Term] terms)
  | multiplication(list[Term] terms)
  | division(Term lhs, Term rhs)
  | modulo(Term lhs, Term rhs) 
  ;

data Literal
  = \int(int i)
  ;

data Command
  = minimize(Formula f)
  | maximize(Formula f)
  ;
	
Sort sortOfLit(\int(_)	) = \int();
	
Term addition(lit(\int(0)), Term rhs) = rhs;
Term addition(Term lhs, lit(\int(0))) = lhs;
Term addition(lit(\int(a)), lit(\int(b))) = lit(\int(a+b));	
Term addition(addition(list[Term] l), Term r) = addition([*l, r]);
Term addition(Term l, addition(list[Term] r)) = addition([l, *r]);
default Term addition(Term lhs, Term rhs) = addition([lhs,rhs]);

Term substraction(lit(\int(0)), Term rhs) = neg(rhs);
Term substraction(Term lhs, lit(\int(0))) = lhs;
Term substraction(lit(\int(a)), lit(\int(b))) = lit(\int(a-b));
default Term substraction(Term lhs, Term rhs) = addition([lhs, neg(rhs)]);

Term multiplication(lit(\int(0)), Term rhs) = lit(\int(0));
Term multiplication(Term lhs, lit(\int(0))) = lit(\int(0));
Term multiplication(lit(\int(1)), Term rhs) = rhs;
Term multiplication(Term lhs, lit(\int(1))) = lhs;
Term multiplication(lit(\int(a)),lit(\int(b))) = lit(\int(a*b));
Term multiplication(multiplication(list[Term] l), Term r) = multiplication([*l, r]);
Term multiplication(Term l, multiplication(list[Term] r)) = multiplication([l, *r]);
default Term multiplication(Term lhs, Term rhs) = multiplication([lhs,rhs]);

Term division(lit(\int(x)), lit(\int(y))) = lit(\int(x/y));
Term modulo(lit(\int(x)),lit(\int(y))) = lit(\int(x%y)); 

Formula lt(lit(\int(x)),lit(\int(y))) = \false() when x >= y;
Formula lt(lit(\int(x)),lit(\int(y))) = \true() when x < y;

Formula lte(lit(\int(x)),lit(\int(y))) = \false() when x > y;
Formula lte(lit(\int(x)),lit(\int(y))) = \true() when x <= y;

Formula gt(lit(\int(x)),lit(\int(y))) = \false() when x <= y;
Formula gt(lit(\int(x)),lit(\int(y))) = \true() when x > y;

Formula gte(lit(\int(x)),lit(\int(y))) = \false() when x < y;
Formula gte(lit(\int(x)),lit(\int(y))) = \true() when x >= y;