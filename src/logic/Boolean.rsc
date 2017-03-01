module logic::Boolean

data Formula
	= \true()
	| \false()
	| \not(Formula f)
	| \and(set[Formula] fs)
	| \or(set[Formula] fs)
	;

Formula \or({})									                      = \false();
Formula \or({Formula x}) 						                  = x;
  
//Formula \or({\false(), *Formula r})   			    = \or(r);
//Formula \or({\true(), *Formula _})   			      = \true();
//Formula \or({*Formula a, or(set[Formula] b)})   = \or(a + b);
//Formula \or({Formula g,\not(g),*Formula r}) 	  = \true();
//
//Formula \or({Formula g, \and({not(g), *Formula ra}), *Formula ro}) = \or({\and({not(g)} + ra)} + ro);
//Formula \or({not(Formula g), \and({g, *Formula ra}), *Formula ro}) = \or({\and({g} + ra)} + ro);

Formula \and({})								                      = \true();
Formula \and({Formula x}) 						                = x;

//Formula \and({\true(), *Formula r})				      = \and(r);
//Formula \and({\false(), *Formula _}) 			      = \false();
//Formula \and({*Formula a, and(set[Formula] b)}) = \and(a + b);
//Formula \and({Formula g,\not(g),*Formula r}) 	  = \false();
//
//Formula \and({Formula g, \or({not(g), *Formula ro}), *Formula ra}) = \and({g,\or(ro)} + ra);  
//Formula \and({not(Formula g), \or({g, *Formula ro}), *Formula ra}) = \and({not(g),\or(ro)} + ra);  

Formula \or(\true(), Formula _)                       = \true();
Formula \or(Formula _, \true())                       = \true();
Formula \or(\false(), Formula b)                      = b;
Formula \or(Formula a, \false())                      = a;
Formula \or(Formula a, \or(clauses))                  = \or({a, *clauses});
Formula \or(Formula a, a)                             = a; 
Formula \or(\not(Formula a), a)                       = \true();
Formula \or(Formula a, \not(a))                       = \true();
Formula \or(Formula a, \or(set[Formula] inner))       = \or({a, *inner});
Formula \or(\or(set[Formula] inner), Formula a)       = \or({a, *inner});
default Formula \or(Formula a, Formula b)             = \or({a,b});

Formula \and(\true(), Formula b)                      = b;
Formula \and(Formula a, \true())                      = a;
Formula \and(\false(), Formula _)                     = \false();
Formula \and(Formula _, \false())                     = \false();
Formula \and(Formula a, \and(clauses))                = \and({a, *clauses});
Formula \and(Formula a, a)                            = a;
Formula \and(Formula a, not(a))                       = \false();
Formula \and(not(Formula a), a)                       = \false();
Formula \and(Formula a, \and(set[Formula] inner))     = \and({a, *inner});
Formula \and(\and(set[Formula] inner), Formula a)     = \and({a, *inner});
default Formula \and(Formula a, Formula b)            = \and({a,b});

Formula \not(not(Formula g)) 					                = g;
Formula \not(\true())        					                = \false();
Formula \not(\false())       					                = \true();

Formula \if(Formula l, Formula r)           	        = \or(\not(l),r);
Formula \fi(Formula l, Formula r)           	        = \if(r, l);
Formula \iff(Formula l, Formula r)          	        = \and(\if(l,r),\fi(l,r));

Formula \ite(Formula c, Formula t, Formula e) 	      = \or(\iff(c,t),\iff(\not(c),e));