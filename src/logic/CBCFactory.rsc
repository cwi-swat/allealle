module logic::CBCFactory

import logic::Integer;

import Set;

//Formula rewrite(\or({}))                                       = \false();
//Formula rewrite(\or({Formula x}))                              = x;
//  
//Formula rewrite(\or({\false(), *Formula r}))                   = \or(r);
//Formula rewrite(\or({\true(), *Formula _}))                    = \true();
//Formula rewrite(\or({Formula g,\not(g),*Formula r}))          = \true();

Formula rewrite(Formula f) {
  int d = 8;
  
  Formula r = f;
  
  while (Formula r1 := rewrite(r, d), r1 != r) {
    r = r1;
  }
  
  return r;
}

Formula rewrite(orig:\or({Formula b, origAnd:\not(\and(set[Formula] andClauses))}), int limit) {
  if (size(andClauses) > limit) { 
     return orig;
  }
  else if (b in andClauses) {
    return \true();
  }
  else if (not(b) in andClauses) {
    return origAnd;
  }
  else return orig; 
}

Formula rewrite(orig:\or({Formula b, origAnd:\and(set[Formula] andClauses)}), int limit) {
  if (size(andClauses) > limit) { 
     return orig;
  }
  else if (not(b) in andClauses) {
    return b;
  } else {
    return orig;
  }
}

Formula rewrite(orig:\or({*Formula orClauses, origAnd:\and(set[Formula] andClauses)}), int limit) {
  if (size(orClauses) > limit || size(andClauses) > limit) {
    return orig;
  } else if (Formula a <- orClauses, a in andClauses) {
    return \or(orClauses);
  } else {
    return orig;
  }
}

Formula rewrite(\or({Formula b, \and({b, *Formula _})}))                  = b;
Formula rewrite(\or({*Formula a, \or(set[Formula] c)}))       = \or({*a,*c});
Formula rewrite(\or({Formula a, *Formula orc, \and({a, Formula* ar})})) = \or({a, *orc}); 

default Formula rewrite(c:\or(set[Formula] clauses))          = c;

Formula \and({})                                      = \true();

Formula \and({Formula x})                             = x;
Formula \and({\true(), *Formula r})                   = \and(r);
Formula \and({\false(), *Formula _})                  = \false();
Formula \and({*Formula a, \and(set[Formula] c)})      = \and({*a,*c});

Formula \and(\true(), Formula b)                      = b;
Formula \and(Formula a, \true())                      = a;

Formula \and(\false(), Formula _)                     = \false();
Formula \and(Formula _, \false())                     = \false();

Formula \and(Formula a, not(a))                       = \false();
Formula \and(not(Formula a), a)                       = \false();

//Formula \and(Formula a, \and(set[Formula] inner))     = \and({a, *inner});
//Formula \and(\and(set[Formula] inner), Formula a)     = \and({a, *inner});

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

Formula \not(not(Formula g))                          = g;
Formula \not(\true())                                 = \false();
Formula \not(\false())                                = \true();

Formula \ite(\true(), Formula t, Formula _)           = t;
Formula \ite(\false(), Formula _, Formula e)          = e;
Formula \ite(Formula _, Formula t, t)                 = t;
//default Formula \ite(Formula c, Formula t, Formula e) = \or(\iff(c,t),\iff(\not(c),e));

Formula \if(Formula l, Formula r)                     = \or(\not(l),r);
Formula \fi(Formula l, Formula r)                     = \if(r, l);
Formula \iff(Formula l, Formula r)                    = \and(\if(l,r),\fi(l,r));
