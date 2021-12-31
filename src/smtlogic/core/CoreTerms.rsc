module smtlogic::core::CoreTerms

data Sort
  = \bool()
  ;

data Formula
	= \true()
	| \false()
	| pvar(str name)
	| \not(Formula f)
	| \and(set[Formula] fs)
	| \or(set[Formula] fs)
	| equal(set[Formula] fs) 
	| equal(set[Term] ts)
	| distinct(set[Term] terms)
	;

data Term
  = lit(Literal l)
  | var(str name, Sort s)
  | ite(Formula c, Term t, Term e)
  | aggregateFunc(str name, Formula exists, Term t, Term accum)
  | aggregateFunc(str name, Formula exists, Term accum) 
  ; 

data Literal
  = ttrue()
  | ffalse()
  | id(str id)
  ;

  
data Command
  = setOption(Option op)
  | maximize(Term t)
  | minimize(Term t)
  ;

data Option
  = optimizationPriority(OptPriority prio)
  ;
  
data OptPriority
  = lexicographic()
  | pareto()
  | independent()
  ;
  
Sort sortOfLit(var(_,Sort s)) = s;
default Sort sortOfLit(Literal l) { throw "Unable to obtain sort of literal \'<l>\'"; }

Formula \or({})            = \false();
Formula \or({Formula x})   = x;  

Formula \and({})           = \true();
Formula \and({Formula x})  = x;

default Formula \or(Formula a, Formula b)             = \or({a,b});
default Formula \and(Formula a, Formula b)            = \and({a,b});
default Formula implies(Formula i, Formula t)         = \or(not(i),t);

Formula equal(Term t, t)                              = \true();
Formula equal(lit(x),lit(y))                          = \false() when x != y;
default Formula equal(Term l, Term r)                 = equal({l,r});
default Formula equal(Formula l, Formula r)           = equal({l,r});


