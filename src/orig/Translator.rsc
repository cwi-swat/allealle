module orig::Translator

import orig::AST;

import IO;
import Relation;

import logic::Propositional;

alias Environment = map[str, Binding];
 
alias Binding = rel[int, Formula];
alias TranslationResult = tuple[Formula formula, map[str, Binding] environment];

TranslationResult translate(Problem p) {
	Environment env = createInitialEnvironment(p.uni, p.bounds);

	Formula formula = (\true() | \and(it, translateFormula(f, env)) | f <- p.formulas, tf := translateFormula(f, env));
	
	return <formula, env>;
} 

Formula translateFormula(empty(Expr expr), Environment env)		 	
	= \not(translateFormula(nonEmpty(expr), env));

Formula translateFormula(atMostOne(Expr expr), Environment env) 	
	= \or(translateFormula(empty(expr), env), translateFormula(exactlyOne(expr), env));

Formula translateFormula(exactlyOne(Expr expr), Environment env) 	
	= (\or({}) | \or(it, \and(x, 
				(\and({}) | \and(it, \not(y)) | int fy <- domain(m), Formula y <- m[fy], fy != fx))) | int fx <- domain(m), Formula x <- m[fx])   
	when Binding m := translateExpr(expr, env);

Formula translateFormula(nonEmpty(Expr expr), Environment env) 			
	= (\or({}) | \or(it, a) | int x <- domain(m), Formula a <- m[x])
	when Binding m := translateExpr(expr, env);

Formula translateFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env) 
	= (\and({}) | \and(it, c) | int idx <- domain(m), Formula c <- m[idx])
	when Binding lhsBin := translateExpr(lhsExpr, env),
		 Binding rhsBin := translateExpr(rhsExpr, env),
		 Binding m := {<idxA, \or(\not(a), b)> | int idxA <- domain(lhsBin), Formula a <- lhsBin[idxA], Formula b <- rhsBin[idxA]};

Formula translateFormula(equal(Expr lhsExpr, Expr rhsExpr), Environment env)
	= \and(translateFormula(subset(lhsExpr, rhsExpr), env), translateFormula(subset(rhsExpr, lhsExpr), env));
	
Formula translateFormula(negation(Formula form), Environment env) 
	= \not(translateFormula(form, env));
	
Formula translateFormula(conjunction(Formula lhsForm, Formula rhsForm), Environment env)
	= \and(translateFormula(lhsForm, env), translateFormula(rhsForm, env));
	
Formula translateFormula(disjunction(Formula lhsForm, Formula rhsForm), Environment env)
	= \or(translateFormula(lhsForm, env), translateFormula(rhsForm, env));
	
Formula tranlsateFormula(implication(Formula lhsForm, Formula rhsForm), Environment env)
	= \or(\not(translateFormula(lhsForm, env)), translateFormula(rhsForm, env));
	
Formula tranlsateFormula(equality(Formula lhsForm, Formula rhsForm), Environment env)
	= \or(\and(translateFormula(lhsForm, env), translateFormula(rhsForm, env)), \and(\not(translateFormula(lhsForm, env)), \not(translateFormula(rhsForm, env))));
	
	//| universal(list[VarDeclaration] decls, Formula form)
	//| existential(list[VarDeclaration] decls, Formula form) 

default Formula translateFormula(Formula f, Environment env) { throw "Translation of formula \'f\' not yet implemented";}

Binding translateExpr(variable(str name), Environment env) = env[name];
//Binding translateExpr(transpose(Expr expr)) = 
	//| closure(Expr expr)
	//| reflexClosure(Expr expr)
	
Binding translateExpr(union(Expr lhs, Expr rhs), Environment env) = m  
	when Binding lhsBin := translateExpr(lhs, env),
		 Binding rhsBin := translateExpr(rhs, env),
		 Binding m := {<idx, \or(a,b)> | int idx <- domain(lhsBin), Formula a <- lhsBin[idx], Formula b <- rhsBin[idx]};
	
	//| intersection(Expr lhs, Expr rhs)
	//| difference(Expr lhs, Expr rhs)
	//| \join(Expr lhs, Expr rhs)
	
Binding translateExpr(product(Expr lhs, Expr rhs), Environment env) = m
	when Binding lhsBin := translateExpr(lhs, env),
		 Binding rhsBin := translateExpr(rhs, env),
		 Binding m := {<idxA, \and(a,b)> | int idxA <- domain(lhsBin), Formula a <- lhsBin[idxA], int idxB <- domain(rhsBin), Formula b <- rhsBin[idxB]};
		 
	//| ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr)
	//| comprehension(list[VarDeclaration] decls, Formula form)

default Binding translateExpr(Expr e, Environment env) { throw "Translation of expression \'<e>\' not yet implemented";}

Environment createInitialEnvironment(Universe uni, list[RelationalBound] relationalBounds) {
	int idx = 0;
	int index() { idx += 1; return idx; }
	void reset() { idx = 0; }	
	
	rel[int, Formula] createRelationalMapping(relationalBound(str relName, 1, list[Tuple] lb, list[Tuple] ub)) =
		{<index(), unaryToFormula(a, lb, ub, relName)> | Atom a <- uni.atoms};
	
	rel[int, Formula] createRelationalMapping(relationalBound(str relName, 2, list[Tuple] lb, list[Tuple] ub)) =
		{<index(), binaryToFormula(a, b, lb, ub, relName)> | Atom a <- uni.atoms, Atom b <- uni.atoms};	
	
	Environment env = ();
	for (RelationalBound rb <- relationalBounds) {
		reset();
		env += (rb.relName: createRelationalMapping(rb));
	}
	
	return env;
}		
		
Formula unaryToFormula(Atom a, list[Tuple] lowerBounds, list[Tuple] upperBounds, str _) = \true() when /\tuple([a]) := lowerBounds;
Formula unaryToFormula(Atom a, list[Tuple] lowerBounds, list[Tuple] upperBounds, str relBound) = var("<relBound>_<a>") when /\tuple([a]) !:= lowerBounds, /\tuple([a]) := upperBounds;
default Formula unaryToFormula(Atom _, list[Tuple] _, list[Tuple] _, str _) = \false(); 
	
Formula binaryToFormula(Atom a, Atom b, list[Tuple] lowerBounds, list[Tuple] upperBounds, str _) = \true() when /\tuple([a,b]) := lowerBounds;
Formula binaryToFormula(Atom a, Atom b, list[Tuple] lowerBounds, list[Tuple] upperBounds, str relBound) = var("<relBound>_<a>_<b>") when /\tuple([a,b]) !:= lowerBounds, /\tuple([a,b]) := upperBounds;
default Formula binaryToFormula(Atom _, Atom _, list[Tuple] _, list[Tuple] _, str _) = \false();