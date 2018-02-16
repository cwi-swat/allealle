module smtlogic::Core

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
  //| implies(Formula \if, Formula \then)
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
  = maximize(Term t)
  | minimize(Term t)
  ;

Sort sortOfLit(var(_,Sort s)) = s;
default Sort sortOfLit(Literal l) { throw "Unable to obtain sort of literal \'<l>\'"; }

Formula \or({})									                      = \false();
Formula \or({Formula x}) 						                  = x;
  
Formula \or({\false(), *Formula r})   			          = \or(r);
Formula \or({\true(), *Formula _})   			            = \true();

Formula \or({*Formula a, \or(set[Formula] b)})         = \or(a + b);

//Formula \or({Formula g,\not(g),*Formula r}) 	  = \true();
//
//Formula \or({Formula g, \and({not(g), *Formula ra}), *Formula ro}) = \or({\and({not(g)} + ra)} + ro);
//Formula \or({not(Formula g), \and({g, *Formula ra}), *Formula ro}) = \or({\and({g} + ra)} + ro);

Formula \and({*Formula a, and(set[Formula] b)}) = \and(a + b);
//Formula \and({Formula g,\not(g),*Formula r}) 	  = \false();
//
//Formula \and({Formula g, \or({not(g), *Formula ro}), *Formula ra}) = \and({g,\or(ro)} + ra);  
//Formula \and({not(Formula g), \or({g, *Formula ro}), *Formula ra}) = \and({not(g),\or(ro)} + ra);  

Formula \or(\true(), Formula _)                       = \true();
Formula \or(Formula _, \true())                       = \true();

Formula \or(\false(), Formula b)                      = b;
Formula \or(Formula a, \false())                      = a;

Formula \or(Formula a, \or(set[Formula] inner))       = \or({a, *inner});
Formula \or(\or(set[Formula] inner), Formula a)       = \or({a, *inner});

Formula \or(\not(Formula a), a)                       = \true();
Formula \or(Formula a, \not(a))                       = \true();

//Formula \or(Formula a, \and({not(a), *Formula rest})) = \or({\and({not(a), *rest})});
//Formula \or(\and({not(Formula a), *Formula rest}), a) = \or({\and({not(a), *rest})});

//Formula \or(not(Formula a), \and({a, *Formula rest})) = \or({\and({a, *rest})});
//Formula \or(\and({Formula a, *Formula rest}), not(a)) = \or({\and({a, *rest})});

Formula \or(Formula a, \and(set[Formula] clauses))    = a when a in clauses; 
Formula \or(\and(set[Formula] clauses), Formula a)    = a when a in clauses;

//Formula \or({*Formula r, \and(set[Formula] l)})       = \or(r) when Formula a <- l, a in r;

Formula \or(\and(set[Formula] l), \and(l))            = \and(l);

default Formula \or(Formula a, Formula b)             = \or({a,b});

Formula \and({})                                      = \true();

Formula \and({Formula x})                             = x;
Formula \and({\true(), *Formula r})                   = \and(r);
Formula \and({\false(), *Formula _})                  = \false();
//Formula \and({*Formula a, \and(set[Formula] c)})      = \and({*a,*c});

Formula \and(\true(), Formula b)                      = b;
Formula \and(Formula a, \true())                      = a;

Formula \and(\false(), Formula _)                     = \false();
Formula \and(Formula _, \false())                     = \false();

Formula \and(Formula a, not(a))                       = \false();
Formula \and(not(Formula a), a)                       = \false();

Formula \and(Formula a, \and(set[Formula] inner))     = \and({a, *inner});
Formula \and(\and(set[Formula] inner), Formula a)     = \and({a, *inner});

//Formula \and(Formula a, \or({not(a), *Formula rest})) = \and({a, \or(rest)});
//Formula \and(\or({not(Formula a), *Formula rest}), a) = \and({a, \or(rest)});
//
//Formula \and(not(Formula a), \or({a, *Formula rest})) = \and({not(a), \or(rest)});
//Formula \and(\or({not(Formula a), *Formula rest}), a) = \and({not(a), \or(rest)});

Formula \and(Formula a, \or(set[Formula] clauses))    = a when a in clauses;
Formula \and(\or(set[Formula] clauses), Formula a)    = a when a in clauses;

//Formula \and({*Formula l, \or(set[Formula] r)})       = \and(l) when Formula a <- l, a in r;

Formula \and(\or(set[Formula] l), \or(l))             = \or(l);

default Formula \and(Formula a, Formula b)            = \and({a,b});

Formula \not(not(Formula g)) 					                = g;
Formula \not(\true())        					                = \false();
Formula \not(\false())       					                = \true();

Term \ite(\true(), Term t, Term _)                    = t;
Term \ite(\false(), Term _, Term e)                   = e;
Term \ite(Formula _, Term t, t)                       = t;
//default Formula \ite(Formula c, Formula t, Formula e) = \or(\iff(c,t),\iff(\not(c),e));

//Formula \if(Formula l, Formula r)           	        = \or(\not(l),r);
//Formula \fi(Formula l, Formula r)           	        = \if(r, l);

Formula implies(\true(), Formula r)                   = r;
Formula implies(\false(), Formula r)                  = \true();
Formula implies(Formula r, \true())                   = \true();
Formula implies(Formula r, \false())                  = r;
Formula implies(Formula f, f)                         = f;
default Formula implies(Formula i, Formula t)         = \or(not(i),t);

Formula equal(Term t, t)                              = \true();
Formula equal(lit(x),lit(y))                          = \false() when x != y;
default Formula equal(Term l, Term r)                 = equal({l,r});

default Formula equal(Formula l, Formula r)           = equal({l,r});


