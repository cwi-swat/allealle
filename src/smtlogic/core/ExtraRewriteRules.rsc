module smtlogic::core::ExtraRewriteRules

import smtlogic::core::CoreTerms;

Formula \or({Formula g,\not(g),*Formula _}) 	  = \true();
Formula \and({Formula g,\not(g),*Formula _})    = \false();

//Formula \or({Formula g, \and({not(g), *Formula ra}), *Formula ro}) = \or({\and({not(g)} + ra)} + ro);
//Formula \or({not(Formula g), \and({g, *Formula ra}), *Formula ro}) = \or({\and({g} + ra)} + ro);

//Formula \and({Formula g, \or({not(g), *Formula ro}), *Formula ra}) = \and({g,\or(ro)} + ra);  
//Formula \and({not(Formula g), \or({g, *Formula ro}), *Formula ra}) = \and({not(g),\or(ro)} + ra);  
//
//Formula \or({Formula a, \and({not(a), *Formula rest}), *Formula rest2}) = \or({\and({not(a), *rest, *rest2})});
//Formula \or(\and({not(Formula a), *Formula rest}), a) = \or({\and({not(a), *rest})});
//
//Formula \or(not(Formula a), \and({a, *Formula rest})) = \or({\and({a, *rest})});
//Formula \or(\and({Formula a, *Formula rest}), not(a)) = \or({\and({a, *rest})});
//
//Formula \or({*Formula r, \and(set[Formula] l)})       = \or(r) when Formula a <- l, a in r;
Formula \or({Formula l, \and({l, *Formula _}), *Formula rest}) = \or({l, *rest});
//
//Formula \and({*Formula a, \and(set[Formula] c)})      = \and({*a,*c});
//
//Formula \and(Formula a, \or({not(a), *Formula rest})) = \and({a, \or(rest)});
//Formula \and(\or({not(Formula a), *Formula rest}), a) = \and({a, \or(rest)});
//
//Formula \and(not(Formula a), \or({a, *Formula rest})) = \and({not(a), \or(rest)});
//Formula \and(\or({not(Formula a), *Formula rest}), a) = \and({not(a), \or(rest)});
//
//Formula \and({*Formula l, \or(set[Formula] r)})       = \and(l) when Formula a <- r, a in l;
Formula \and({Formula l, \or({l, *Formula _}), *Formula rest}) = \and({l, *rest});