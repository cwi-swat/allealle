module orig::FormulaTranslator

import orig::AST;
import orig::ExpressionTranslator;

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
	= (\true() | \and(it, translateFormula(f, env, p.uni)) | f <- p.formulas);

Formula translateFormula(empty(Expr expr), Environment env, Universe uni) = \not(translateFormula(nonEmpty(expr), env, uni));

Formula translateFormula(atMostOne(Expr expr), Environment env, Universe uni) 	
	= \or(translateFormula(empty(expr), env, uni), translateFormula(exactlyOne(expr), env, uni));

Formula translateFormula(exactlyOne(Expr expr), Environment env, Universe uni) 	
	= (\false() | \or(it, \and(m[x], (\true() | \and(it, \not(m[y])) | Index y <- m, y != x))) | Index x <- m)    
	when Binding m := translateExpr(expr, env, uni);

Formula translateFormula(nonEmpty(Expr expr), Environment env, Universe uni) 			
	= (\false() | \or(it,  m[x]) | Index x <- m)
	when Binding m := translateExpr(expr, env, uni);

Formula translateFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) 
	= m == () ? \false() : (\true() | \and(it, m[x]) | Index x <- m)
	when Binding lhs := translateExpr(lhsExpr, env, uni),
		 Binding rhs := translateExpr(rhsExpr, env, uni),
		 Binding m :=(idx:\or({\not(lhsVal), rhsVal}) | Index idx <- (lhs + rhs), Formula lhsVal := ((idx in lhs) ? lhs[idx] : \false()), Formula rhsVal := ((idx in rhs) ? rhs[idx] : \false())); 
		 
Formula translateFormula(equal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni)
	= \and(translateFormula(subset(lhsExpr, rhsExpr), env, uni), translateFormula(subset(rhsExpr, lhsExpr), env, uni));
	
Formula translateFormula(negation(Formula form), Environment env, Universe uni) 
	= \not(translateFormula(form, env, uni));
	
Formula translateFormula(conjunction(Formula lhsForm, Formula rhsForm), Environment env, Universe uni)
	= \and(translateFormula(lhsForm, env, uni), translateFormula(rhsForm, env, uni));
	
Formula translateFormula(disjunction(Formula lhsForm, Formula rhsForm), Environment env, Universe uni)
	= \or(translateFormula(lhsForm, env, uni), translateFormula(rhsForm, env, uni));
	
Formula translateFormula(implication(Formula lhsForm, Formula rhsForm), Environment env, Universe uni)
	= \or(\not(translateFormula(lhsForm, env, uni)), translateFormula(rhsForm, env, uni));
	
Formula translateFormula(equality(Formula lhsForm, Formula rhsForm), Environment env, Universe uni)
	= \or(\and(translateFormula(lhsForm, env, uni),  translateFormula(rhsForm, env, uni)), \and(\not(translateFormula(lhsForm, env, uni)), \not(translateFormula(rhsForm, env, uni))));

Formula translateFormula(universal(list[VarDeclaration] decls, Formula form), Environment env, Universe uni) 
	= \and({\or({\not(m[x]), translateFormula(f, env + (hd.name:getSingletonBinding(x)), uni)}) | Index x <- m, Formula f := (([] == t) ? form : universal(t, form))})
	when [VarDeclaration hd, *t] := decls,
	     Binding m := translateExpr(hd.binding, env, uni);
	 
Formula translateFormula(existential(list[VarDeclaration] decls, Formula form), Environment env, Universe uni)
	= \or({\and({m[x], translateFormula(f, env + (hd.name:getSingletonBinding(x)), uni)}) | Index x <- m, Formula f := (([] == t) ? form : existential(t, form))}) 
	when [VarDeclaration hd, *t] := decls,
	     Binding m := translateExpr(hd.binding, env, uni);
	     	
default Formula translateFormula(Formula f, Environment env, Universe uni) { throw "Translation of formula \'<f>\' with function \'<translateFormula>\' not yet implemented";}

@memo
Binding getSingletonBinding(Index x) = (x:\true()); 

Binding translateExpr(variable(str name), Environment env, Universe uni) = env[name];

Binding translateExpr(transpose(Expr expr), Environment env, Universe uni) = transpose(m, uni)
	when Binding m := translateExpr(expr, env, uni); 

Binding translateExpr(closure(Expr expr), Environment env, Universe uni) = transitiveClosure(m, uni)
	when Binding m := translateExpr(expr, env, uni);
		 
Binding translateExpr(reflexClosure(Expr expr), Environment env, Universe uni) = reflexiveTransitiveClosure(m, uni)
	when Binding m := translateExpr(expr, env, uni);
		
Binding translateExpr(union(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = disjunction(lhs,rhs)  
	when Binding lhs := translateExpr(lhsExpr, env, uni),
		   Binding rhs := translateExpr(rhsExpr, env, uni);
	
Binding translateExpr(intersection(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = conjunction(lhs, rhs)
	when Binding lhs := translateExpr(lhsExpr, env, uni),
		   Binding rhs := translateExpr(rhsExpr, env, uni);

Binding translateExpr(difference(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = 
	(x:\and(lhs[x],rhsVal) | Index x <- lhs, Formula rhsVal := ((x notin rhs) ? \true() : \not(rhs[x])))
	when Binding lhs := translateExpr(lhsExpr, env, uni),
		   Binding rhs := translateExpr(rhsExpr, env, uni);

Binding translateExpr(\join(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = \join(lhs, rhs) 
	when Binding lhs := translateExpr(lhsExpr, env, uni),
		   Binding rhs := translateExpr(rhsExpr, env, uni);
		
Binding translateExpr(product(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = product(lhs, rhs)
	when Binding lhs := translateExpr(lhsExpr, env, uni),
		   Binding rhs := translateExpr(rhsExpr, env, uni);

Binding translateExpr(ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr), Environment env, Universe uni)
	 = (idx:ite(translateFormula(caseForm, env, uni),p[idx],q[idx]) | Index idx <- p)
	when Binding p := translateExpr(thenExpr, env, uni),
		   Binding q := translateExpr(elseExpr, env, uni);
		 
//Binding translateExpr(comprehension(list[VarDeclaration] decls, Formula form), Environment env) {
//	Index flatten([<Atom a, relTheory()>]) = <a, relTheory()>;
//	Index flatten([<Atom a, relTheory()>, <Atom b, relTheory()>]) = <a,b, relTheory()>;
//	Index flatten([<Atom a, relTheory()>, <Atom b, relTheory()>, <Atom c, relTheory()>]) = <a,b,c, relTheory()>;
//	
//	Binding getVal(list[Index] currentIndex, Environment extendedEnv, int currentDecl, Formula declConstraints) {
//		if (currentDecl == size(decls)) {
//			return (flatten(currentIndex):\and(declConstraints, translateFormula(form, env + extendedEnv)));
//		}
//		
//		VarDeclaration decl = decls[currentDecl];
//		Binding m = translateExpr(decl.binding, env + extendedEnv);
//				
//		Binding result = ();
//		for (Index idx <- m) {
//			result += getVal([*currentIndex, idx], extendedEnv + (decl.name:getSingletonBinding(idx)), currentDecl + 1, \and(declConstraints, m[idx]));
//		}		
//		
//		return result; 
//	}
//	
//	Binding result = getVal([], env, 0, \true());
//	
//	return result;	
//}
	
default Binding translateExpr(Expr e, Environment env, Universe uni) { throw "Translation of expression \'<e>\' not yet implemented";}

Binding createRelationalMapping(relationalBound(str relName, int arity, list[Tuple] lb, list[Tuple] ub)) {
  str idxToStr(Index idx) = intercalate("_", idx);
  
  Binding result = (idx : \true() | \tuple(list[Atom] idx) <- lb);
  result += (idx : var("<relName>_<idxToStr(idx)>") | \tuple(list[Atom] idx) <- ub, idx notin result);
  
  return result;
} 
