module logic::Propositional

extend logic::Boolean;
//extend lang::logic::ast::Booleans;

data Formula
	= var(str x)
	;
