module orig::Translator

import orig::AST;

import IO;
import List;
import Relation;
import Map;

import logic::Propositional;

alias Environment = map[str, Binding];

// index is a tuple of different arity
alias Index = value;
//alias Index = list[Atom];
alias Binding = map[Index, Formula]; 
 
alias TranslationResult = tuple[Formula formula, map[str, Binding] environment];

TranslationResult translate(Problem p) {
	Environment env = createInitialEnvironment(p.uni, p.bounds);
	//println(env);
	Formula formula = (\true() | \and(it, translateFormula(f, env)) | f <- p.formulas);
	
	return <formula, env>;
} 

Formula translateFormula(empty(Expr expr), Environment env)		 	
	= \not(translateFormula(nonEmpty(expr), env));

Formula translateFormula(atMostOne(Expr expr), Environment env) 	
	= \or(translateFormula(empty(expr), env), translateFormula(exactlyOne(expr), env));

Formula translateFormula(exactlyOne(Expr expr), Environment env) 	
	= (\false() | \or(it, \and(m[x], (\true() | \and(it, \not(m[y])) | Index y <- m, y != x))) | Index x <- m)    
	when Binding m := translateExpr(expr, env);

Formula translateFormula(nonEmpty(Expr expr), Environment env) 			
	= (\false() | \or(it,  m[x]) | Index x <- m)
	when Binding m := translateExpr(expr, env);

Formula translateFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env) 
	= (\true() | \and(it, m[x]) | Index x <- m)
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env),
		 Binding m := (x:\or(\not(lhs[x]), rhs[x]) | Index x <- lhs);
		 
Formula translateFormula(equal(Expr lhsExpr, Expr rhsExpr), Environment env)
	= \and(translateFormula(subset(lhsExpr, rhsExpr), env), translateFormula(subset(rhsExpr, lhsExpr), env));
	
Formula translateFormula(negation(Formula form), Environment env) 
	= \not(translateFormula(form, env));
	
Formula translateFormula(conjunction(Formula lhsForm, Formula rhsForm), Environment env)
	= \and(translateFormula(lhsForm, env), translateFormula(rhsForm, env));
	
Formula translateFormula(disjunction(Formula lhsForm, Formula rhsForm), Environment env)
	= \or(translateFormula(lhsForm, env), translateFormula(rhsForm, env));
	
Formula translateFormula(implication(Formula lhsForm, Formula rhsForm), Environment env)
	= \or(\not(translateFormula(lhsForm, env)), translateFormula(rhsForm, env));
	
Formula translateFormula(equality(Formula lhsForm, Formula rhsForm), Environment env)
	= \or(\and(translateFormula(lhsForm, env), translateFormula(rhsForm, env)), \and(\not(translateFormula(lhsForm, env)), \not(translateFormula(rhsForm, env))));

Binding createSingletonBinding(Binding orig, Index x) =
	(y:val | Index y <- orig, Formula val := ((y == x) ? \true() : \false()));
	
Formula translateFormula(universal(list[VarDeclaration] decls, Formula form), Environment env) 
	= \and({\or({\not(m[x]), translateFormula(f, env + (hd.name:createSingletonBinding(m,x)))}) | Index x <- m, Formula f := (([] == t) ? form : universal(t, form))})
	when [VarDeclaration hd, *t] := decls,
	     Binding m := translateExpr(hd.binding, env);
	 
Formula translateFormula(existential(list[VarDeclaration] decls, Formula form), Environment env)
	= \or({\and({m[x], translateFormula(f, env + (hd.name:createSingletonBinding(m,x)))}) | Index x <- m, Formula f := (([] == t) ? form : existential(t, form))}) 
	when [VarDeclaration hd, *t] := decls,
	     Binding m := translateExpr(hd.binding, env);
	     	
default Formula translateFormula(Formula f, Environment env) { throw "Translation of formula \'<f>\' not yet implemented";}

int arity(Binding b) = 1 when /tuple[Atom] _ := domain(b);
int arity(Binding b) = 2 when /tuple[Atom,Atom] _ := domain(b);
default int arity(Binding b) { throw "Relations with an arity greater then 2 are not allowed";}

bool sameArity(Binding lhs, Binding rhs) = arity(lhs) == arity(rhs); 

Binding translateExpr(variable(str name), Environment env) = env[name];

//Binding translateExpr(transpose(Expr expr)) = 
	//| closure(Expr expr)
	//| reflexClosure(Expr expr)
	
Binding translateExpr(union(Expr lhsExpr, Expr rhsExpr), Environment env) = m  
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env),
		 sameArity(lhs, rhs),
		 Binding m := (x:\or(lhs[x],rhs[x]) | Index x <- lhs);
default Binding translateExpr(union(Expr lhsExpr, Expr rhsExpr), _) {throw "Cannot create an union between <lhsExpr> and <rhsExpr>";}
	
Binding translateExpr(intersection(Expr lhsExpr, Expr rhsExpr), Environment env) = m
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env),
		 sameArity(lhs, rhs),
		 Binding m := (x:\and(lhs[x],rhs[x]) | Index x <- lhs);
default Binding translateExpr(intersection(Expr lhsExpr, Expr rhsExpr), _) {throw "Cannot create an intersection between <lhsExpr> and <rhsExpr>";}


	//| difference(Expr lhs, Expr rhs)

Binding translateExpr(\join(Expr lhsExpr, Expr rhsExpr), Environment env) = m 
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env),
		 Binding m := performJoin(arity(lhs), arity(rhs), lhs, rhs);
default Binding translateExpr(\join(Expr lhsExpr, Expr rhsExpr), _) {throw "Cannot join <lhsExpr> and <rhsExpr>";}
	
Binding performJoin(1, 1, Binding lhs, Binding rhs) { throw "Cannot join two relations of arity 1";}	

Binding performJoin(1, 2, Binding lhs, Binding rhs)	
	= (row:\or({\and({lhs[<x>], rhs[y]}) | <Atom x> <- domain(lhs), /Index y:<x, row> := domain(rhs)}) | <Atom row> <- domain(lhs));

Binding performJoin(2, 1, Binding lhs, Binding rhs) 
	= (row:\or({\and({lhs[idx], rhs[<x>]}) | /Index idx:<row, Atom x> := domain(lhs)}) | /<Atom row, _> := domain(lhs));
	
Binding performJoin(2, 2, Binding lhs, Binding rhs) 
	= (idx:\or(lhs[idx],\and({rhs[y] | /Index y:<x, other> := domain(rhs)})) | Atom x <- range(domain(lhs)), Index idx:<Atom other, x> <- domain(lhs));
	
default Binding performJoin(int arityLhs, int arityRhs, Binding lhs, Binding rhs) { throw "Unsupported join of relations with arity <arityLhs> and <arityRhs>";}
	
Binding translateExpr(product(Expr lhsExpr, Expr rhsExpr), Environment env) = m
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env),
		 sameArity(lhs,rhs),
		 Binding m := performProduct(arity(lhs), arity(rhs), lhs, rhs);
default Binding translateExpr(product(Expr lhsExpr, Expr rhsExpr), _) {throw "Cannot create a product between <lhsExpr> and <rhsExpr>";}

Binding performProduct(1, 1, Binding lhs, Binding rhs)
	= (<a,b>:\and(lhs[x],rhs[y]) | x:<Atom a> <- lhs, y:<Atom b> <- rhs);

Binding performProduct(2, 2, Binding lhs, Binding rhs)
	= (<aa,ab,ba,bb>:\and(lhs[x],rhs[y]) | <Atom aa, _> <- lhs, x:<aa, Atom ab> := lhs, <Atom ba, _> <- rhs, y:<ba, Atom bb> := rhs);

	//| ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr)
	//| comprehension(list[VarDeclaration] decls, Formula form)

default Binding translateExpr(Expr e, Environment env) { throw "Translation of expression \'<e>\' not yet implemented";}

Environment createInitialEnvironment(Universe uni, list[RelationalBound] relationalBounds) =
	(rb.relName: createRelationalMapping(rb, uni) | RelationalBound rb <- relationalBounds);
	
map[Index, Formula] createRelationalMapping(relationalBound(str relName, 1, list[Tuple] lb, list[Tuple] ub), Universe uni) =
	(<a>:f | Atom a <- uni.atoms, Formula f := unaryToFormula(a, lb, ub, relName));

map[Index, Formula] createRelationalMapping(relationalBound(str relName, 2, list[Tuple] lb, list[Tuple] ub), Universe uni) =
	(<a,b>:f | Atom a <- uni.atoms, Atom b <- uni.atoms, Formula f := binaryToFormula(a, b, lb, ub, relName));	

default map[Index, Formula] createRelationalMapping(RelationalBound b, Universe _) {throw "RelationalBounds with an arity of <b.arity> are not yet supported";}
		
Formula unaryToFormula(Atom a, list[Tuple] lowerBounds, list[Tuple] upperBounds, str _) = \true() when /\tuple([a]) := lowerBounds;
Formula unaryToFormula(Atom a, list[Tuple] lowerBounds, list[Tuple] upperBounds, str relBound) = var("<relBound>_<a>") when /\tuple([a]) !:= lowerBounds, /\tuple([a]) := upperBounds;
default Formula unaryToFormula(Atom _, list[Tuple] _, list[Tuple] _, str _) = \false(); 
	
Formula binaryToFormula(Atom a, Atom b, list[Tuple] lowerBounds, list[Tuple] upperBounds, str _) = \true() when /\tuple([a,b]) := lowerBounds;
Formula binaryToFormula(Atom a, Atom b, list[Tuple] lowerBounds, list[Tuple] upperBounds, str relBound) = var("<relBound>_<a>_<b>") when /\tuple([a,b]) !:= lowerBounds, /\tuple([a,b]) := upperBounds;
default Formula binaryToFormula(Atom _, Atom _, list[Tuple] _, list[Tuple] _, str _) = \false();

Formula tenaryToFormula(Atom a, Atom b, Atom c, list[Tuple] lowerBounds, list[Tuple] upperBounds, str _) = \true() when /\tuple([a,b,c]) := lowerBounds;
Formula tenaryToFormula(Atom a, Atom b, Atom c, list[Tuple] lowerBounds, list[Tuple] upperBounds, str relBound) = var("<relBound>_<a>_<b>_<c>") when /\tuple([a,b,c]) !:= lowerBounds, /\tuple([a,b,c]) := upperBounds;
default Formula tenaryToFormula(Atom _, Atom _, Atom _, list[Tuple] _, list[Tuple] _, str _) = \false();