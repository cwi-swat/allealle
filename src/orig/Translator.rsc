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

Environment createInitialEnvironment(Problem p) 
	= (rb.relName:createRelationalMapping(rb) | RelationalBound rb <- p.bounds);

Formula translate(Problem p, Environment env) 
	= (\true() | \and(it, translateFormula(f, env + binaryIdentity(p.uni) + emptyUnary(p.uni) + emptyBinary(p.uni))) | f <- p.formulas);

Binding getConstant(Binding orig, Environment env) = getConstant(orig, env, arity(orig));
Binding getConstant(Binding orig, Environment env, 1) = env["_emptyUnary"];
Binding getConstant(Binding orig, Environment env, 2) = env["_emptyBinary"];

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
	= m == () ? \false() : (\true() | \and(it, m[x]) | Index x <- m)
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env),
		 //Binding m := \or(not(lhs, getConstant(lhs, env)), rhs); 
		 Binding m :=(idx:\or({\not(lhsVal), rhsVal}) | Index idx <- (lhs + rhs), Formula lhsVal := ((idx in lhs) ? lhs[idx] : \false()), Formula rhsVal := ((idx in rhs) ? rhs[idx] : \false())); 
		 
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
	= \or(\and(translateFormula(lhsForm, env),  translateFormula(rhsForm, env)), \and(\not(translateFormula(lhsForm, env)), \not(translateFormula(rhsForm, env))));

Formula translateFormula(universal(list[VarDeclaration] decls, Formula form), Environment env) 
	= \and({\or({\not(m[x]), translateFormula(f, env + (hd.name:getSingletonBinding(x)))}) | Index x <- m, Formula f := (([] == t) ? form : universal(t, form))})
	when [VarDeclaration hd, *t] := decls,
	     Binding m := translateExpr(hd.binding, env);
	 
Formula translateFormula(existential(list[VarDeclaration] decls, Formula form), Environment env)
	= \or({\and({m[x], translateFormula(f, env + (hd.name:getSingletonBinding(x)))}) | Index x <- m, Formula f := (([] == t) ? form : existential(t, form))}) 
	when [VarDeclaration hd, *t] := decls,
	     Binding m := translateExpr(hd.binding, env);
	     	
default Formula translateFormula(Formula f, Environment env) { throw "Translation of formula \'<f>\' with function \'<translateFormula>\' not yet implemented";}

@memo
Binding getSingletonBinding(Index x) = (x:\true()); 

Binding translateExpr(variable(str name), Environment env) = env[name];

Binding translateExpr(transpose(Expr expr), Environment env) = transpose(m)
	when Binding m := translateExpr(expr, env); 

Binding translateExpr(closure(Expr expr), Environment env) = square(m, 1)
	when Binding m := translateExpr(expr, env);
		 
Binding translateExpr(reflexClosure(Expr expr), Environment env) = \or(m, env["_binId"])  
	when Binding m := translateExpr(closure(expr), env);
		
Binding translateExpr(union(Expr lhsExpr, Expr rhsExpr), Environment env) = \or(lhs,rhs)  
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env);
	
Binding translateExpr(intersection(Expr lhsExpr, Expr rhsExpr), Environment env) = \and(lhs, rhs)
	when Binding lhs := translateExpr(lhsExpr, env),
		 Binding rhs := translateExpr(rhsExpr, env);

Binding translateExpr(difference(Expr lhsExpr, Expr rhsExpr), Environment env) = 
	(x:\and(lhs[x],rhsVal) | Index x <- lhs, Formula rhsVal := ((x notin rhs) ? \true() : \not(rhs[x])))
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
		 
Binding translateExpr(comprehension(list[VarDeclaration] decls, Formula form), Environment env) {
	Index flatten([<Atom a, relTheory()>]) = <a, relTheory()>;
	Index flatten([<Atom a, relTheory()>, <Atom b, relTheory()>]) = <a,b, relTheory()>;
	Index flatten([<Atom a, relTheory()>, <Atom b, relTheory()>, <Atom c, relTheory()>]) = <a,b,c, relTheory()>;
	
	Binding getVal(list[Index] currentIndex, Environment extendedEnv, int currentDecl, Formula declConstraints) {
		if (currentDecl == size(decls)) {
			return (flatten(currentIndex):\and(declConstraints, translateFormula(form, env + extendedEnv)));
		}
		
		VarDeclaration decl = decls[currentDecl];
		Binding m = translateExpr(decl.binding, env + extendedEnv);
				
		Binding result = ();
		for (Index idx <- m) {
			result += getVal([*currentIndex, idx], extendedEnv + (decl.name:getSingletonBinding(idx)), currentDecl + 1, \and(declConstraints, m[idx]));
		}		
		
		return result; 
	}
	
	Binding result = getVal([], env, 0, \true());
	
	return result;	
}
	
default Binding translateExpr(Expr e, Environment env) { throw "Translation of expression \'<e>\' not yet implemented";}
	
Binding createRelationalMapping(relationalBound(str relName, 1, list[Tuple] lb, list[Tuple] ub)) 
	= (<a, relTheory()>:\true() | \tuple([Atom a]) <- lb) + (<a, relTheory()>:var("<relName>_<a>") | \tuple([Atom a]) <- ub, \tuple([a]) notin lb); 

Binding createRelationalMapping(relationalBound(str relName, 2, list[Tuple] lb, list[Tuple] ub)) 
	= (<a,b, relTheory()>:\true() | \tuple([Atom a, Atom b]) <- lb) + (<a,b, relTheory()>:var("<relName>_<a>_<b>") | \tuple([Atom a, Atom b]) <- ub, \tuple([a,b]) notin lb);	

default Binding createRelationalMapping(relationalBound(str relName, int arity, list[Tuple] _, list[Tuple] _)) {throw "RelationalBounds with an arity of <b.arity> are not yet supported";}

Environment binaryIdentity(Universe uni) = ("_binId":(<a,a, relTheory()>:\true() | Atom a <- uni.atoms));
Environment emptyUnary(Universe uni) = ("_emptyUnary":(<a, relTheory()>:\true() | Atom a <- uni.atoms));
Environment emptyBinary(Universe uni) = ("_emptyBinary":(<a,b, relTheory()>:\true() | Atom a <- uni.atoms, Atom b <- uni.atoms));