module orig::Translator

import orig::AST;

import IO;
import Relation;

data SATFormula
	= \true()
	| \false()
	| var(str id)
	| not(SATFormula formula)
	| and(set[SATFormula] formulas)
	| or(set[SATFormula] formulas)
	| ite(SATFormula caseCond, SATFormula thenCond, SATFormula elseCond)
	| zero()
	;

data Index
	= unary(str a)
	| binary(str a, str b)
	//= unary(tuple[int] index)
	//| binary(tuple[int, int] index)
	;
	
alias Environment = tuple[Binding (str) lookup, bool (str, Binding) add];

alias Binding = rel[Index, SATFormula];
alias TranslationResult = tuple[SATFormula formula, map[str, Binding] environment];

//		SATFormula simplify(not(not(SATFormula f))) = f;
//		SATFormula simplify(not(\true())) = \false();
//		SATFormula simplify(not(\false())) = \true();
//		SATFormula simplify(and(\false(),_)) = \false();
//		SATFormula simplify(and(_,\false())) = \false();
//		SATFormula simplify(and(\true(),rhs)) = rhs;
//		SATFormula simplify(and(lhs,\true())) = lhs;
//		SATFormula simplify(and(\true(),\true())) = \true();
//		SATFormula simplify(or(\true(),_)) = \true();
//		SATFormula simplify(or(_,\true())) = \true();
//		SATFormula simplify(or(\false(),rhs)) = rhs;
//		SATFormula simplify(or(lhs,\false())) = lhs;
//		SATFormula simplify(or(\false(),\false())) = \false();
//default	SATFormula simplify(SATFormula orig) = orig;
		
TranslationResult translate(Problem p) {
	map[str, Binding] envInternal = ();

	Binding lookupFromInternal(str name) = envInternal[name];
	bool addToInternal(str name, Binding vb) { envInternal[name] = vb; return true; }

	Environment env = <lookupFromInternal, addToInternal>;
	
	fillInitialEnvironment(p.uni, p.bounds, env);

	SATFormula formula = (and({}) | consAnd(it, translateFormula(f, env)) | f <- p.formulas, tf := translateFormula(f, env), bprintln(tf));
	//formula = bottom-up visit(formula) {
	//	case SATFormula f => simplify(f)
	//}
	
	return <formula, envInternal>;
} 

SATFormula consNot(\true()) = \false();
SATFormula consNot(\false()) = \true();
SATFormula consNot(not(not(SATFormula f))) = f;
SATFormula consNot(zero()) = zero();
default SATFormula consNot(SATFormula f) = not(f);

SATFormula consAnd(zero(), _) = zero();
SATFormula consAnd(_, zero()) = zero();
SATFormula consAnd(SATFormula lhs, SATFormula rhs) = consAnd(consAnd(and({}), rhs), lhs) when and(_) !:= lhs;
SATFormula consAnd(and(_), \false()) = and({\false()});
SATFormula consAnd(and({\false()}), _) = and({\false()});
SATFormula consAnd(orig:and(_), \true()) = orig;
default SATFormula consAnd(and(set[SATFormula] orig), SATFormula new) = and(orig + new);

SATFormula consOr(zero(), _) = zero();
SATFormula consOr(_, zero()) = zero();
SATFormula consOr(SATFormula lhs, SATFormula rhs) = consOr(consOr(or({}), rhs), lhs) when or(_) !:= lhs;
SATFormula consOr(or(_), \true()) = or({\true()});
SATFormula consOr(or({\true()}), _) = or({\true()});
SATFormula consOr(orig:or(_), \false()) = orig;
default SATFormula consOr(or(set[SATFormula] orig), SATFormula new) = or(orig + new);

SATFormula translateFormula(empty(Expr expr), Environment env)		 	
	= not(translateFormula(atMostOne(expr), env));

SATFormula translateFormula(atMostOne(Expr expr), Environment env) 	
	= consOr(tranlateFormula(empty(expr), env), translateFormula(exactlyOne(expr), env));

SATFormula translateFormula(exactlyOne(Expr expr), Environment env) 	
	= (or({}) | consOr(it, consAnd(x, 
				(and({}) | consAnd(it, consNot(y)) | Index fy <- domain(m), SATFormula y <- m[fy], y != \false(), y != x))) | Index fx <- domain(m), SATFormula x <- m[fx], x != \false())   
	when Binding m := translateExpr(expr, env);

SATFormula translateFormula(nonEmpty(Expr expr), Environment env) 			
	= (or({}) | consOr(it, a) | Index x <- domain(vb), SATFormula a <- m[x], a != \false())
	when Binding m := translateExpr(expr, env);

SATFormula translateFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env) = (and({}) | consAnd(it, c) | Index idx <- domain(m), SATFormula c <- m[idx], c != zero())
	when Binding lhsBin := translateExpr(lhsExpr, env),
		 Binding rhsBin := translateExpr(rhsExpr, env),
		 Binding m := {<unary("<idxA.a>"), consOr(consNot(a), b)> | Index idxA <- domain(lhsBin), SATFormula a <- lhsBin[idxA], SATFormula b <- rhsBin[idxA], bprintln("idx=<idxA>, a=<a>, b=<b>")};
		 //bprintln(m); 

	//| equal(Expr lhsExpr, Expr rhsExpr)
	//| negation(Formula form)
	//| conjunction(Formula lhsForm, Formula rhsForm)
	//| disjunction(Formula lhsForm, Formula rhsForm)
	//| implication(Formula lhsForm, Formula rhsForm)
	//| equality(Formula lhsForm, Formula rhsForm)
	//| universal(list[VarDeclaration] decls, Formula form)
	//| existential(list[VarDeclaration] decls, Formula form) 

Binding translateExpr(variable(str name), Environment env) = env.lookup(name);
//Binding translateExpr(transpose(Expr expr)) = 
	//| closure(Expr expr)
	//| reflexClosure(Expr expr)
Binding translateExpr(union(Expr lhs, Expr rhs), Environment env) = m  
	when Binding lhsBin := translateExpr(lhs, env),
		 Binding rhsBin := translateExpr(rhs, env),
		 Binding m := {<idx, consOr(a,b)> | Index idx <- domain(lhsBin), SATFormula a <- lhsBin[idx], SATFormula b <- rhsBin[idx]},
		 bprintln(m); 
	//| intersection(Expr lhs, Expr rhs)
	//| difference(Expr lhs, Expr rhs)
	//| \join(Expr lhs, Expr rhs)
Binding translateExpr(product(Expr lhs, Expr rhs), Environment env) = m
	when Binding lhsBin := translateExpr(lhs, env),
		 Binding rhsBin := translateExpr(rhs, env),
		 Binding m := {<idxA, consAnd(a,b)> | Index idxA <- domain(lhsBin), SATFormula a <- lhsBin[idxA], Index idxB <- domain(rhsBin), SATFormula b <- rhsBin[idxB]};
		 
	//| ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr)
	//| comprehension(list[VarDeclaration] decls, Formula form)

default Binding translateExpr(Expr e, Environment env) { throw "Translation of expression \'<e>\' not yet implemented";}


void fillInitialEnvironment(Universe uni, list[RelationalBound] relationalBounds, Environment env) {
	rel[Index, SATFormula] createRelationalMapping(relationalBound(str relName, 1, list[Tuple] lb, list[Tuple] ub)) =
		{<unary("<a>"), unaryToSATFormula(a, lb, ub, relName)> | Atom a <- uni.atoms};
	
	rel[Index, SATFormula] createRelationalMapping(relationalBound(str relName, 2, list[Tuple] lb, list[Tuple] ub)) =
		{<binary("<a>", "<b>"), binaryToSATFormula(a, b, lb, ub, relName)> | Atom a <- uni.atoms, Atom b <- uni.atoms};	
	
	for (RelationalBound rb <- relationalBounds) {
		env.add(rb.relName, createRelationalMapping(rb));
	}
}		
		
		SATFormula unaryToSATFormula(Atom a, list[Tuple] lowerBounds, list[Tuple] upperBounds, str _) 			= \true() 
			when /\tuple([a]) := lowerBounds;
		SATFormula unaryToSATFormula(Atom a, list[Tuple] lowerBounds, list[Tuple]	upperBounds, str relBound) 	= var("<relBound>_<a>") 
			when /\tuple([a]) !:= lowerBounds, /\tuple([a]) := upperBounds;
default SATFormula unaryToSATFormula(Atom _, list[Tuple] _, 			list[Tuple] _		   , str _) 		= \zero(); 
	
		SATFormula binaryToSATFormula(Atom a, Atom b, list[Tuple] lowerBounds, list[Tuple] upperBounds, str _) 			= \true() 
			when /\tuple([a,b]) := lowerBounds;
		SATFormula binaryToSATFormula(Atom a, Atom b, list[Tuple] lowerBounds, list[Tuple] upperBounds, str relBound) 	= var("<relBound>_<a>_<b>") 
			when /\tuple([a,b]) !:= lowerBounds, /\tuple([a,b]) := upperBounds;
default SATFormula binaryToSATFormula(Atom _, Atom _, list[Tuple] _		   	 , list[Tuple] _		  , str _) 			= \zero();
