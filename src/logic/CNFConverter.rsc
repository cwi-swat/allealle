module logic::CNFConverter

import logic::Propositional;

Formula convertToCNF(Formula orig) {
	// Formula only consist of and, or, not and var so not necessary to rewrite implication and equality
	if (/true() := orig || /false() := orig) {
		throw "Original formula can only contain \'not\', \'and\', \'or\' or \'var\'";
	}
	
	return toCNF(toNNF(orig));
}

Formula toNNF(orig:\var(_)) = orig;
Formula toNNF(\not(\and(set[Formula] clauses))) = \or({\not(toNNF(c)) | c <- clauses}); 
Formula toNNF(\not(\or(set[Formula] clauses))) = \and({\not(toNNF(c)) | c <- clauses});
Formula toNNF(orig:\not(Formula _)) = orig;
default Formula toNNF(\and(set[Formula] clauses)) = \and({toNNF(c) | c <- clauses});
default Formula toNNF(\or(set[Formula] clauses)) = \or({toNNF(c) | c <- clauses});

Formula toCNF(orig:\var(_)) = orig;
Formula toCNF(orig:\not(_)) = orig;
Formula toCNF(\or({\and(set[Formula] andClauses), *Formula r})) = \and({toCNF(\or(c + r)) | c <- andClauses});
default Formula toCNF(\or(set[Formula] clauses)) = \or({toCNF(c) | c <- clauses});
default Formula toCNF(\and(set[Formula] clauses)) = \and({toCNF(c) | c <- clauses});
default Formula toCNF(Formula f) = f;
