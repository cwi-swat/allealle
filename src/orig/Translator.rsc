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
	;

//data Index
//	= unary(str a)
//	| binary(str a, str b)
//	;
	
alias Environment = tuple[Binding (str) lookup, bool (str, Binding) add];

//alias Binding = rel[Index, SATFormula];
alias Binding = rel[int, SATFormula];
alias TranslationResult = tuple[SATFormula formula, map[str, Binding] environment];

SATFormula simplify(or({})) = \false();
SATFormula simplify(or({SATFormula singleElem})) = singleElem; 
SATFormula simplify(and({})) = \true();
SATFormula simplify(and({SATFormula singleElem})) = singleElem;
default	SATFormula simplify(SATFormula orig) = orig;
		
TranslationResult translate(Problem p) {
	map[str, Binding] envInternal = ();

	Binding lookupFromInternal(str name) = envInternal[name];
	bool addToInternal(str name, Binding vb) { envInternal[name] = vb; return true; }

	Environment env = <lookupFromInternal, addToInternal>;
	
	fillInitialEnvironment(p.uni, p.bounds, env);

	SATFormula formula = (and({}) | consAnd(it, translateFormula(f, env)) | f <- p.formulas, tf := translateFormula(f, env));
	
	formula = bottom-up visit(formula) {
		case SATFormula f => simplify(f)
	}
	
	return <formula, envInternal>;
} 

SATFormula consNot(\true()) = \false();
SATFormula consNot(\false()) = \true();
SATFormula consNot(not(not(SATFormula f))) = f;
default SATFormula consNot(SATFormula f) = not(f);

SATFormula consAnd(\false(), _) = \false();
SATFormula consAnd(SATFormula lhs, SATFormula rhs) = consAnd(consAnd(and({}), rhs), lhs) when and(_) !:= lhs;
SATFormula consAnd(and(_), \false()) = \false();
SATFormula consAnd(and({\false()}), _) = \false();
SATFormula consAnd(orig:and(_), \true()) = orig;
default SATFormula consAnd(and(set[SATFormula] orig), SATFormula new) = and(orig + new);

SATFormula consOr(\true(),_) = \true();
SATFormula consOr(SATFormula lhs, SATFormula rhs) = consOr(consOr(or({}), rhs), lhs) when or(_) !:= lhs;
SATFormula consOr(or(_), \true()) = \true();
SATFormula consOr(or({\true()}), _) = \true();
SATFormula consOr(orig:or(_), \false()) = orig;
default SATFormula consOr(or(set[SATFormula] orig), SATFormula new) = or(orig + new);

SATFormula translateFormula(empty(Expr expr), Environment env)		 	
	= not(translateFormula(atMostOne(expr), env));

SATFormula translateFormula(atMostOne(Expr expr), Environment env) 	
	= consOr(tranlateFormula(empty(expr), env), translateFormula(exactlyOne(expr), env));

SATFormula translateFormula(exactlyOne(Expr expr), Environment env) 	
	= (or({}) | consOr(it, consAnd(x, 
				(and({}) | consAnd(it, consNot(y)) | int fy <- domain(m), SATFormula y <- m[fy], y != x))) | int fx <- domain(m), SATFormula x <- m[fx])   
	when Binding m := translateExpr(expr, env);

SATFormula translateFormula(nonEmpty(Expr expr), Environment env) 			
	= (or({}) | consOr(it, a) | Index x <- domain(vb), SATFormula a <- m[x])
	when Binding m := translateExpr(expr, env);

SATFormula translateFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env) = (and({}) | consAnd(it, c) | int idx <- domain(m), SATFormula c <- m[idx])
	when Binding lhsBin := translateExpr(lhsExpr, env),
		 Binding rhsBin := translateExpr(rhsExpr, env),
		 Binding m := {<idxA, consOr(consNot(a), b)> | int idxA <- domain(lhsBin), SATFormula a <- lhsBin[idxA], SATFormula b <- rhsBin[idxA]};

	//| equal(Expr lhsExpr, Expr rhsExpr)
	//| negation(Formula form)
	//| conjunction(Formula lhsForm, Formula rhsForm)
	//| disjunction(Formula lhsForm, Formula rhsForm)
	//| implication(Formula lhsForm, Formula rhsForm)
	//| equality(Formula lhsForm, Formula rhsForm)
	//| universal(list[VarDeclaration] decls, Formula form)
	//| existential(list[VarDeclaration] decls, Formula form) 

default SATFormula translateFormula(Formula f, Environment env) { throw "Translation of formula \'f\' not yet implemented";}

Binding translateExpr(variable(str name), Environment env) = env.lookup(name);
//Binding translateExpr(transpose(Expr expr)) = 
	//| closure(Expr expr)
	//| reflexClosure(Expr expr)
	
Binding translateExpr(union(Expr lhs, Expr rhs), Environment env) = m  
	when Binding lhsBin := translateExpr(lhs, env),
		 Binding rhsBin := translateExpr(rhs, env),
		 Binding m := {<idx, consOr(a,b)> | int idx <- domain(lhsBin), SATFormula a <- lhsBin[idx], SATFormula b <- rhsBin[idx]};
	
	//| intersection(Expr lhs, Expr rhs)
	//| difference(Expr lhs, Expr rhs)
	//| \join(Expr lhs, Expr rhs)
	
Binding translateExpr(product(Expr lhs, Expr rhs), Environment env) = m
	when Binding lhsBin := translateExpr(lhs, env),
		 Binding rhsBin := translateExpr(rhs, env),
		 Binding m := {<idxA, consAnd(a,b)> | int idxA <- domain(lhsBin), SATFormula a <- lhsBin[idxA], int idxB <- domain(rhsBin), SATFormula b <- rhsBin[idxB]};
		 
	//| ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr)
	//| comprehension(list[VarDeclaration] decls, Formula form)

default Binding translateExpr(Expr e, Environment env) { throw "Translation of expression \'<e>\' not yet implemented";}

void fillInitialEnvironment(Universe uni, list[RelationalBound] relationalBounds, Environment env) {
	int idx = 0;
	int index() { idx += 1; return idx; }
	void reset() { idx = 0; }	
	
	rel[int, SATFormula] createRelationalMapping(relationalBound(str relName, 1, list[Tuple] lb, list[Tuple] ub)) =
		{<index(), unaryToSATFormula(a, lb, ub, relName)> | Atom a <- uni.atoms};
	
	rel[int, SATFormula] createRelationalMapping(relationalBound(str relName, 2, list[Tuple] lb, list[Tuple] ub)) =
		{<index(), binaryToSATFormula(a, b, lb, ub, relName)> | Atom a <- uni.atoms, Atom b <- uni.atoms};	
	
	for (RelationalBound rb <- relationalBounds) {
		reset();
		env.add(rb.relName, createRelationalMapping(rb));
	}
}		
		
SATFormula unaryToSATFormula(Atom a, list[Tuple] lowerBounds, list[Tuple] upperBounds, str _) = \true() when /\tuple([a]) := lowerBounds;
SATFormula unaryToSATFormula(Atom a, list[Tuple] lowerBounds, list[Tuple] upperBounds, str relBound) = var("<relBound>_<a>") when /\tuple([a]) !:= lowerBounds, /\tuple([a]) := upperBounds;
default SATFormula unaryToSATFormula(Atom _, list[Tuple] _, list[Tuple] _, str _) = \false(); 
	
SATFormula binaryToSATFormula(Atom a, Atom b, list[Tuple] lowerBounds, list[Tuple] upperBounds, str _) = \true() when /\tuple([a,b]) := lowerBounds;
SATFormula binaryToSATFormula(Atom a, Atom b, list[Tuple] lowerBounds, list[Tuple] upperBounds, str relBound) = var("<relBound>_<a>_<b>") when /\tuple([a,b]) !:= lowerBounds, /\tuple([a,b]) := upperBounds;
default SATFormula binaryToSATFormula(Atom _, Atom _, list[Tuple] _, list[Tuple] _, str _) = \false();
