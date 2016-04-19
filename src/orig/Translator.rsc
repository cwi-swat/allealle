module orig::Translator

import orig::AST;

//import IO;
import Relation;

data BoolFormula
	= \false()
	| \true()
	| var(str id)
	| not(BoolFormula formula)
	| and(set[BoolFormula] formulas)
	| or(set[BoolFormula] formulas)
	| ite(BoolFormula caseCond, BoolFormula thenCond, BoolFormula elseCond)
	;

data Index
	= unary(str a)
	| binary(str a, str b)
	;
	
alias VarBinding = rel[Index, BoolFormula];
alias Environment = map[str, VarBinding];
alias TranslationResult = tuple[BoolFormula formula, Environment env];

private BoolFormula add(and(set[BoolFormula] orig), BoolFormula newForms) = and(orig + newForms);
private BoolFormula add(or(set[BoolFormula] orig), BoolFormula newForms) = or(orig + newForms);

TranslationResult translate(Problem p) {
	BoolFormula translateFormula(empty(Expr expr)) = not(translateFormula(atMostOne(expr)));
	BoolFormula translateFormula(atMostOne(Expr expr)) = or([tranlateFormula(empty(expr), env), translateFormula(exactlyOne(expr))]);
	BoolFormula translateFormula(exactlyOne(Expr expr)) = (or({}) | add(it, and(x + {not(y) | Index fy <- domain(m), BoolFormula y <- m[fy], y != x}))| Index fx <- domain(m), BoolFormula x <- m[fx]) 
		when VarBinding m := translateExpr(expr);
	BoolFormula translateFormula(nonEmpty(Expr expr)) = (or({}) | add(it, m[x]) | Index x <- domain(vb))
		when VarBinding m := translateExpr(expr);
	BoolFormula translateFormula(subset(Expr lhsExpr, Expr rhsExpr)) = ();
		//| equal(Expr lhsExpr, Expr rhsExpr)
		//| negation(Formula form)
		//| conjunction(Formula lhsForm, Formula rhsForm)
		//| disjunction(Formula lhsForm, Formula rhsForm)
		//| implication(Formula lhsForm, Formula rhsForm)
		//| equality(Formula lhsForm, Formula rhsForm)
		//| universal(list[VarDeclaration] decls, Formula form)
		//| existential(list[VarDeclaration] decls, Formula form) 
	
	VarBinding translateExpr(variable(str name)) = env[name];
	//VarBinding translateExpr(transpose(Expr expr)) = 
		//| closure(Expr expr)
		//| reflexClosure(Expr expr)
		//| union(Expr lhs, Expr rhs) 
		//| intersection(Expr lhs, Expr rhs)
		//| difference(Expr lhs, Expr rhs)
		//| \join(Expr lhs, Expr rhs)
		//| product(Expr lhs, Expr rhs)
		//| ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr)
		//| comprehension(list[VarDeclaration] decls, Formula form)
	
	Environment env = createEnvironment(p.uni, p.bounds);

	return <(and({}) | add(it, translateFormula(f)) | f <- p.formulas), env>;
} 


Environment createEnvironment(Universe uni, list[RelationalBound] relationalBounds) {
	int index = 0; 
	
	int newIndex() {
		index += 1;
		return index;
	}

	rel[Index, BoolFormula] createRelationalMapping(relationalBound(str relName, 1, list[Tuple] lb, list[Tuple] ub)) =
		{<unary("<a>"), unaryToBoolFormula(a, lb, ub, relName, newIndex)> | Atom a <- uni.atoms};
	
	rel[Index, BoolFormula] createRelationalMapping(relationalBound(str relName, 2, list[Tuple] lb, list[Tuple] ub)) =
		{<binary("<a>", "<b>"), binaryToBoolFormula(a, b, lb, ub, relName, newIndex)> | Atom a <- uni.atoms, Atom b <- uni.atoms};	
	
	return (() | it + (rb.relName:createRelationalMapping(rb)) | RelationalBound rb <- relationalBounds);	
}		
		
		BoolFormula unaryToBoolFormula(Atom a, list[Tuple] lowerBounds, list[Tuple] upperBounds, str _			, int() _) 		= \true() 
			when /\tuple([a]) := lowerBounds;
		BoolFormula unaryToBoolFormula(Atom a, list[Tuple] lowerBounds, list[Tuple]	upperBounds, str relBound	, int() index) 	= var("<relBound><index()>") 
			when /\tuple([a]) !:= lowerBounds, /\tuple([a]) := upperBounds;
default BoolFormula unaryToBoolFormula(Atom _, list[Tuple] _, 			list[Tuple] _		   , str _			, int() _) 		= \false(); 
	
		BoolFormula binaryToBoolFormula(Atom a, Atom b, list[Tuple] lowerBounds, list[Tuple] upperBounds, str _			, int _) 		= \true() 
			when /\tuple([a,b]) := lowerBounds;
		BoolFormula binaryToBoolFormula(Atom a, Atom b, list[Tuple] lowerBounds, list[Tuple] upperBounds, str relBound	, int index) 	= var("<relBound><index>") 
			when /\tuple([a,b]) !:= lowerBounds, /\tuple([a,b]) := upperBounds;
default BoolFormula binaryToBoolFormula(Atom _, Atom _, list[Tuple] _		   , list[Tuple] _			, str _			, int _) 		= \false();
