module smtlogic::core::RewriteRules

import smtlogic::core::CoreTerms;

Formula \or({*Formula a, \or(set[Formula] b)})        = \or(a + b);
Formula \and({*Formula a, and(set[Formula] b)}) 	    = \and(a + b);

Formula \or(\false(), Formula b)                      = b;
Formula \or(Formula a, \false())                      = a;

Formula \or(Formula a, \or(set[Formula] inner))       = \or({a, *inner});
Formula \or(\or(set[Formula] inner), Formula a)       = \or({a, *inner});

Formula \or(\not(Formula a), a)                       = \true();
Formula \or(Formula a, \not(a))                       = \true();

Formula \or(Formula a, \and(set[Formula] clauses))    = a when a in clauses; 
Formula \or(\and(set[Formula] clauses), Formula a)    = a when a in clauses;

Formula \or(\and(set[Formula] l), \and(l))            = \and(l);

Formula \and(\true(), Formula b)                      = b;
Formula \and(Formula a, \true())                      = a;

Formula \and(Formula a, not(a))                       = \false();
Formula \and(not(Formula a), a)                       = \false();

Formula \and(Formula a, \and(set[Formula] inner))     = \and({a, *inner});
Formula \and(\and(set[Formula] inner), Formula a)     = \and({a, *inner});

Formula \and(Formula a, \or(set[Formula] clauses))    = a when a in clauses;
Formula \and(\or(set[Formula] clauses), Formula a)    = a when a in clauses;

Formula \and(\or(set[Formula] l), \or(l))             = \or(l);

Formula \not(not(Formula g)) 					      = g;
Formula \not(\true())        					      = \false();
Formula \not(\false())       					      = \true();

Term \ite(\true(), Term t, Term _)                    = t;
Term \ite(\false(), Term _, Term e)                   = e;
Term \ite(Formula _, Term t, t)                       = t;

Formula implies(\true(), Formula r)                   = r;
Formula implies(\false(), Formula r)                  = \true();
Formula implies(Formula r, \true())                   = \true();
Formula implies(Formula r, \false())                  = r;
Formula implies(Formula f, f)                         = f;

Formula equal(Term t, t)                              = \true();
Formula equal(lit(x),lit(y))                          = \false() when x != y;
