module orig::Translator

import orig::AST;
import orig::Binder;

import IO;
import List;
import Relation;
import Map;
import Set;

import logic::Propositional;

alias Environment = map[str, Binding];

alias TranslationResult = tuple[Formula formula, map[str, Binding] environment];

TranslationResult translate(Problem p) {
	Environment env = createInitialEnvironment(p.uni, p.bounds);
	Formula formula = (\true() | \and(it, translateFormula(f, env)) | f <- p.formulas);
	
	return <formula, env>;
} 

Formula translateFormula(empty(Expr expr), Environment env) = \not(translateFormula(nonEmpty(expr), env));

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
		 Binding m := \or(not(lhs), rhs); 
		 
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

Formula translateFormula(universal(list[VarDeclaration] decls, Formula form), Environment env) 
	= \and({\or({\not(m[x]), translateFormula(f, env + (hd.name:getSingletonBinding(m,x)))}) | Index x <- m, Formula f := (([] == t) ? form : universal(t, form))})
	when [VarDeclaration hd, *t] := decls,
	     Binding m := translateExpr(hd.binding, env);
	 
Formula translateFormula(existential(list[VarDeclaration] decls, Formula form), Environment env)
	= \or({\and({m[x], translateFormula(f, env + (hd.name:getSingletonBinding(m,x)))}) | Index x <- m, Formula f := (([] == t) ? form : existential(t, form))}) 
	when [VarDeclaration hd, *t] := decls,
	     Binding m := translateExpr(hd.binding, env);
	     	
default Formula translateFormula(Formula f, Environment env) { throw "Translation of formula \'<f>\' not yet implemented";}

Binding getSingletonBinding(Binding orig, Index x, Environment env) = createSingletonBinding(env["emptyUnary"], x) when arity(m) == 1; 
Binding getSingletonBinding(Binding orig, Index x, Environment env) = createSingletonBinding(env["emptyBinary"], x) when arity(m) == 2;
default Binding getSingletonBinding(Binding orig, Index x, Environment env) { throw "Can not create singleton binding for relation with arity <arity>"; }

Binding translateExpr(variable(str name), Environment env) = env[name];

Binding translateExpr(transpose(Expr expr), Environment env) = transpose(m)
	when Binding m := translateExpr(expr, env); 

Binding translateExpr(closure(Expr expr), Environment env) = square(m, 1)
	when Binding m := translateExpr(expr, env);
		 
Binding translateExpr(reflexClosure(Expr expr), Environment env) = \or(m, env["binId"])  
	when Binding m := translateExpr(closure(expr), env);
		
Binding translateExpr(union(Expr lhsExpr, Expr rhsExpr), Environment env) = \or(lhs,rhs)  
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env);
	
Binding translateExpr(intersection(Expr lhsExpr, Expr rhsExpr), Environment env) = \and(lhs, rhs)
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env);

Binding translateExpr(difference(Expr lhsExpr, Expr rhsExpr), Environment env) = \and(lhs, not(rhs))
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env);

Binding translateExpr(\join(Expr lhsExpr, Expr rhsExpr), Environment env) = \join(lhs, rhs) 
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env);
		
Binding translateExpr(product(Expr lhsExpr, Expr rhsExpr), Environment env) = product(lhs, rhs)
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env);

Binding translateExpr(ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr), Environment env)
	 = (idx:ite(translateFormula(caseForm, env),p[idx],q[idx]) | Index idx <- p)
	when Binding p := translateExpr(thenExpr, env),
		 Binding q := translateExpr(elseExpr, env);
		 
//Binding translateExpr(comprehension(list[VarDeclaration] decls, Formula form), Environment env) = m
//	when [VarDeclaration hd, *t] := decls,
		
	
default Binding translateExpr(Expr e, Environment env) { throw "Translation of expression \'<e>\' not yet implemented";}

Environment createInitialEnvironment(Universe uni, list[RelationalBound] relationalBounds) 
	= (rb.relName: createRelationalMapping(rb, uni) | RelationalBound rb <- relationalBounds) + binaryIdentity(uni) + emptyUnary(uni) + emptyBinary(uni);
	
map[Index, Formula] createRelationalMapping(relationalBound(str relName, 1, list[Tuple] lb, list[Tuple] ub), Universe uni) 
	= (<a>:f | Atom a <- uni.atoms, Formula f := unaryToFormula(a, lb, ub, relName), f != \false());

map[Index, Formula] createRelationalMapping(relationalBound(str relName, 2, list[Tuple] lb, list[Tuple] ub), Universe uni) 
	= (<a,b>:f | Atom a <- uni.atoms, Atom b <- uni.atoms, Formula f := binaryToFormula(a, b, lb, ub, relName), f != \false());	

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

Binding binaryIdentity(Universe uni) = ("_binId":(<a,a>:\true() | Atom a <- uni.atoms));
Binding emptyUnary(Universe uni) = ("_emptyUnary":(<a>:\true() | Atom a <- uni.atoms));
Binding emptyBinary(Universe uni) = ("_emptyBinary":(<a,b>:\true() | Atom a <- uni.atoms, Atom b <- uni.atoms));