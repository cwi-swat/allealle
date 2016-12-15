module logic::Boolean

data Formula
	= \true()
	| \false()
	| \not(Formula f)
	| \and(set[Formula] fs)
	| \or(set[Formula] fs)
	;

Formula \or({})									                    = \false();
Formula \or({Formula x}) 						                = x;
Formula \or(Formula a, Formula b) 				          = \or({a,b});

@memo Formula \or({\false(), *Formula r})   			  = \or(r);
@memo Formula \or({\true(), *Formula _})   			    = \true();
@memo Formula \or({*Formula a, or(set[Formula] b)}) = \or(a + b);
@memo Formula \or({Formula g,\not(g),*Formula r}) 	= \true();

@memo Formula \or({Formula g, \and({not(g), *Formula ra}), *Formula ro}) = \or({\and({not(g)} + ra)} + ro);
@memo Formula \or({not(Formula g), \and({g, *Formula ra}), *Formula ro}) = \or({\and({g} + ra)} + ro);

Formula \and({})								= \true();
Formula \and({Formula x}) 						= x;

Formula \and(Formula a, Formula b) 				= \and({a,b});

@memo
Formula \and({\true(), *Formula r})				= \and(r);
@memo
Formula \and({\false(), *Formula _}) 			= \false();
@memo
Formula \and({*Formula a, and(set[Formula] b)}) = \and(a + b);
@memo
Formula \and({Formula g,\not(g),*Formula r}) 	= \false();

@memo
Formula \and({Formula g, \or({not(g), *Formula ro}), *Formula ra}) = \and({g,\or(ro)} + ra);  
@memo
Formula \and({not(Formula g), \or({g, *Formula ro}), *Formula ra}) = \and({not(g),\or(ro)} + ra);  

Formula \not(not(Formula g)) 					= g;
Formula \not(\true())        					= \false();
Formula \not(\false())       					= \true();

Formula \if(Formula l, Formula r)           	= \or(\not(l),r);
Formula \fi(Formula l, Formula r)           	= \if(r, l);
Formula \iff(Formula l, Formula r)          	= \and(\if(l,r),\fi(l,r));

Formula \ite(Formula c, Formula t, Formula e) 	= \or(\iff(c,t),\iff(\not(c),e));