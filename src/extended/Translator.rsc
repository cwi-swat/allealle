module extended::Translator

extend orig::Translator;

import logic::Integer;
import extended::Binder;

Binding createRelationalMapping(relationalBound(str relName, intSort(), 1, list[Tuple] lb, list[Tuple] ub)) 
	= (<a, intTheory()>:intVar("<relName>_<a>") | \tuple([Atom a]) <- ub) + 
	  createRelationalMapping(relationalBound(relName, 1, lb, ub)); 

default Environment createRelationalMapping(relationalBound(str relName, Sort s, int arity, list[Tuple] _, list[Tuple] _))
	{throw "Unable to create initial binding for relation <relName> of sort <s> with arity <arity>";}

Formula translateExtended(Problem p, Environment env) 
	= (\true() | \and(it, translateExtFormula(f, env + binaryIdentity(p.uni) + emptyUnary(p.uni) + emptyBinary(p.uni))) | f <- p.formulas);

Formula translateExtFormula(empty(Expr expr), Environment env) = \not(translateExtFormula(nonEmpty(expr), env));

Formula translateExtFormula(atMostOne(Expr expr), Environment env) 	
	= \or(translateExtFormula(empty(expr), env), translateExtFormula(exactlyOne(expr), env));

Formula translateExtFormula(exactlyOne(Expr expr), Environment env) 	
	= (\false() | \or(it, \and(m[x], (\true() | \and(it, \not(m[y])) | Index y <- m, y != x))) | Index x <- m)    
	when Binding m := translateExtExpr(expr, env);

Formula translateExtFormula(nonEmpty(Expr expr), Environment env) 			
	= (\false() | \or(it,  m[x]) | Index x <- m)
	when Binding m := translateExtExpr(expr, env);

Formula translateExtFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env) 
	= m == () ? \false() : (\true() | \and(it, m[x]) | Index x <- m)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env),
		 //Binding m := \or(not(lhs, getConstant(lhs, env)), rhs); 
		 Binding m := (idx:\or({\not(lhsVal), rhsVal}) | Index idx <- (lhs + rhs), /relTheory() := idx, Formula lhsVal := ((idx in lhs) ? lhs[idx] : \false()), Formula rhsVal := ((idx in rhs) ? rhs[idx] : \false())); 
		 
Formula translateExtFormula(equal(Expr lhsExpr, Expr rhsExpr), Environment env)
	= \and(translateExtFormula(subset(lhsExpr, rhsExpr), env), translateExtFormula(subset(rhsExpr, lhsExpr), env));
	
Formula translateExtFormula(negation(Formula form), Environment env) 
	= \not(translateExtFormula(form, env));
	
Formula translateExtFormula(conjunction(Formula lhsForm, Formula rhsForm), Environment env)
	= \and(translateExtFormula(lhsForm, env), translateExtFormula(rhsForm, env));
	
Formula translateExtFormula(disjunction(Formula lhsForm, Formula rhsForm), Environment env)
	= \or(translateExtFormula(lhsForm, env), translateExtFormula(rhsForm, env));
	
Formula translateExtFormula(implication(Formula lhsForm, Formula rhsForm), Environment env)
	= \or(\not(translateExtFormula(lhsForm, env)), translateExtFormula(rhsForm, env));
	
Formula translateExtFormula(equality(Formula lhsForm, Formula rhsForm), Environment env)
	= \or(\and(translateExtFormula(lhsForm, env),  translateExtFormula(rhsForm, env)), \and(\not(translateExtFormula(lhsForm, env)), \not(translateExtFormula(rhsForm, env))));

Formula translateExtFormula(universal(list[VarDeclaration] decls, Formula form), Environment env) 
	= \and({\or({\not(m[x]), translateExtFormula(f, env + (hd.name:getSingletonBinding(x)))}) | Index x <- m, Formula f := (([] == t) ? form : universal(t, form))})
	when [VarDeclaration hd, *t] := decls,
	     Binding m := translateExtExpr(hd.binding, env);
	 
Formula translateExtFormula(existential(list[VarDeclaration] decls, Formula form), Environment env)
	= \or({\and({m[x], translateExtFormula(f, env + (hd.name:getSingletonBinding(x)))}) | Index x <- m, Formula f := (([] == t) ? form : existential(t, form))}) 
	when [VarDeclaration hd, *t] := decls,
	     Binding m := translateExtExpr(hd.binding, env);

Formula translateExtFormula(gt(Expr lhsExpr, Expr rhsExpr), Environment env) = (\true() | \and(it, val) | Index idx:<Atom a,relTheory()> <- m, Formula val := \or(not(m[idx]), m[<a, intTheory()>]))
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env),
		 arity(lhs) == 1 && arity(rhs) == 1,
		 Binding m := (idx:\and(lhs[idx],rhs[idx]) | Index idx:<Atom _, relTheory()> <- lhs) + 
		 			  (<a,intTheory()>:gt(lhs[<a, intTheory()>], rhs[<a, intTheory()>]) | Index idx:<Atom a, relTheory()> <- lhs);

Formula translateExtFormula(lt(Expr lhsExpr, Expr rhsExpr), Environment env) = (\true() | \and(it, val) | Index idx:<Atom a,relTheory()> <- m, Formula val := \or(not(m[idx]), m[<a, intTheory()>]))
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env),
		 arity(lhs) == 1 && arity(rhs) == 1,
		 Binding m := (idx:\and(lhs[idx],rhs[idx]) | Index idx:<Atom _, relTheory()> <- lhs) + 
		 			  (<a,intTheory()>:lt(lhs[<a, intTheory()>], rhs[<a, intTheory()>]) | Index idx:<Atom a, relTheory()> <- lhs);


default Formula translateExtFormula(Formula f, Environment env) { throw "Translation of extended formula \'<f>\' not yet implemented";}

Binding translateExtExpr(variable(str name), Environment env) = env[name];

Binding translateExtExpr(transpose(Expr expr), Environment env) = transpose(m)
	when Binding m := translateExtExpr(expr, env); 

Binding translateExtExpr(closure(Expr expr), Environment env) = square(m, 1)
	when Binding m := translateExtExpr(expr, env);
		 
Binding translateExtExpr(reflexClosure(Expr expr), Environment env) = \or(m, env["_binId"])  
	when Binding m := translateExtExpr(closure(expr), env);
		
Binding translateExtExpr(union(Expr lhsExpr, Expr rhsExpr), Environment env) = \or(lhs,rhs)  
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);

Binding translateExtExpr(\join(Expr lhsExpr, Expr rhsExpr), Environment env) = \join(lhs, rhs) 
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);
		
Binding translateExtExpr(product(Expr lhsExpr, Expr rhsExpr), Environment env) = product(lhs, rhs)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);

Binding translateExtExpr(ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr), Environment env)
	 = (idx:ite(translateExtFormula(caseForm, env),p[idx],q[idx]) | Index idx <- p)
	when Binding p := translateExtExpr(thenExpr, env),
		 Binding q := translateExtExpr(elseExpr, env);
		 
Binding translateExtExpr(comprehension(list[VarDeclaration] decls, Formula form), Environment env) {
	Index flatten([<Atom a, relTheory()>]) = <a, relTheory()>;
	Index flatten([<Atom a, relTheory()>, <Atom b, relTheory()>]) = <a,b, relTheory()>;
	Index flatten([<Atom a, relTheory()>, <Atom b, relTheory()>, <Atom c, relTheory()>]) = <a,b,c, relTheory()>;
	
	Binding getVal(list[Index] currentIndex, Environment extendedEnv, int currentDecl, Formula declConstraints) {
		if (currentDecl == size(decls)) {
			return (flatten(currentIndex):\and(declConstraints, translateExtFormula(form, env + extendedEnv)));
		}
		
		VarDeclaration decl = decls[currentDecl];
		Binding m = translateExtExpr(decl.binding, env + extendedEnv);
				
		Binding result = ();
		for (Index idx <- m) {
			result += getVal([*currentIndex, idx], extendedEnv + (decl.name:getSingletonBinding(idx)), currentDecl + 1, \and(declConstraints, m[idx]));
		}		
		
		return result; 
	}
	
	Binding result = getVal([], env, 0, \true());
	
	return result;	
}
	
//Binding translateExtFormulaExpr(e:variable(str name), Environment env) = translateExtExpr(e,env);
//Binding translateExtFormulaExpr(e:transpose(Expr expr), Environment env) = translateExtExpr(e,env);
//Binding translateExtFormulaExpr(e:closure(Expr expr), Environment env) = translateExtExpr(e,env);
//Binding translateExtFormulaExpr(e:reflexClosure(Expr expr), Environment env) = translateExtExpr(e,env);
//Binding translateExtFormulaExpr(e:union(Expr lhsExpr, Expr rhsExpr), Environment env) = translateExtExpr(e,env);

Binding translateExtExpr(intersection(Expr lhsExpr, Expr rhsExpr), Environment env) = \and(lhs, rhs) +
	(idx:lhs[idx] | Index idx:<Atom _, intTheory()> <- lhs) // TODO: Not yet correct
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);		

Binding translateExtExpr(difference(Expr lhsExpr, Expr rhsExpr), Environment env) = 
	(x:\and(lhs[x],rhsVal) | Index x <- lhs, /relTheory() := x, Formula rhsVal := ((x notin rhs) ? \true() : \not(rhs[x]))) +
	(idx:lhs[idx] | Index idx:<Atom _, intTheory()> <- lhs) // TODO: Not yet correct
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);		

//Binding translateExtFormulaExpr(e:\join(Expr lhsExpr, Expr rhsExpr), Environment env) = translateExtExpr(e,env);
//Binding translateExtFormulaExpr(e:product(Expr lhsExpr, Expr rhsExpr), Environment env) = translateExtExpr(e,env);
//Binding translateExtFormulaExpr(e:ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr), Environment env) = translateExtExpr(e,env);
//Binding translateExtFormulaExpr(e:comprehension(list[VarDeclaration] decls, Formula form), Environment env) = translateExtExpr(e,env);

@memo
Binding translateExtExpr(e:intLit(int i), Environment env) = (<a, intTheory()>:\int(i) | <Atom a,_> <- env["_emptyUnary"]) + (<a, relTheory()>:\true() | <Atom a,_> <- env["_emptyUnary"]);

//Binding translateExtExpr(e:intProjection(Expr expr), Environment env) = translateExtExpr(expr, env);

Binding translateExtExpr(multiplication(Expr lhsExpr, Expr rhsExpr), Environment env) = multiply(lhs, rhs)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);

	//| division(Expr lhs, Expr rhs)
	//| addition(Expr lhs, Expr rhs)
	//| subtraction(Expr lhs, Expr rhs)

default Binding translateExtExpr(Expr e, Environment env) { throw "Translation of extended expression \'<e>\' not yet implemented";}

