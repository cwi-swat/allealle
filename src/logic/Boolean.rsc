module logic::Boolean

data Formula
	= \true()
	| \false()
	| \not(Formula f)
	| \and(set[Formula] fs)
	| \or(set[Formula] fs)
	;

Formula \or({Formula x}) 						= x;
Formula \or({\false(), *Formula r})   			= \or(r);
Formula \or({\true(), *Formula _})   			= \true();
Formula \or(Formula a, Formula b) 				= \or({a,b});
Formula \or({*Formula a, or(set[Formula] b)}) 	= \or(a + b);
Formula \or({Formula g,\not(g),*Formula r}) 	= \true();
//Formula \or({Formula g,and({\not(g), *Formula restOfAnd}),*Formula restOfOr}) 	= \or({g,\and(restOfAnd),*restOfOr});

Formula \and({Formula x}) 						= x;
Formula \and(Formula a, Formula b) 				= \and({a,b});
Formula \and({*Formula a, and(set[Formula] b)}) = \and(a + b);
Formula \and({\true(), *Formula r})				= \and(r);
Formula \and({\false(), *Formula _}) 			= \false();
Formula \and({Formula g,\not(g),*Formula r}) 	= \false();
//Formula \and({Formula g, \or({not(g), *Formula restOfOr}), *Formula restOfAnd})	= \and({g,\or(restOfOr),*restOfAnd});

Formula \not(not(Formula g)) 					= g;
Formula \not(\true())        					= \false();
Formula \not(\false())       					= \true();

Formula \if(Formula l, Formula r)           	= \or(\not(l),r);
Formula \fi(Formula l, Formula r)           	= \if(r, l);
Formula \iff(Formula l, Formula r)          	= \and(\if(l,r),\fi(l,r));

Formula \ite(Formula c, Formula t, Formula e) 	= \or(\iff(c,t),\iff(\not(c),e));