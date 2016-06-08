module extended::Translator

extend orig::Translator;

import logic::Integer;
import extended::Binder;
import extended::AST;

Binding createRelationalMapping(relationalBound(str relName, intSort(), 1, list[Tuple] lb, list[Tuple] ub)) 
	= (<a, intTheory()>:intVar("<a>") | \tuple([Atom a]) <- ub) + 
	  createRelationalMapping(relationalBound(relName, 1, lb, ub)); 

default Environment createRelationalMapping(relationalBound(str relName, Sort s, int arity, list[Tuple] _, list[Tuple] _))
	{throw "Unable to create initial binding for relation <relName> of sort <s> with arity <arity>";}

Formula translateExtended(Problem p, Environment env) 
	= (\true() | \and(it, translateExtFormula(f, env + binaryIdentity(p.uni) + emptyUnary(p.uni) + emptyBinary(p.uni))) | f <- p.formulas);

Formula translateExtFormula(empty(Expr expr), Environment env) = \not(translateExtFormula(nonEmpty(expr), env));

Formula translateExtFormula(atMostOne(Expr expr), Environment env) 	
	= \or(translateExtFormula(empty(expr), env), translateExtFormula(exactlyOne(expr), env));

Formula translateExtFormula(exactlyOne(Expr expr), Environment env) 	
	= (\false() | \or(it, \and(m[x], (\true() | \and(it, \not(m[y])) | Index y <- m, /relTheory() := y, y != x))) | Index x <- m, /relTheory() := x)    
	when Binding m := translateExtExpr(expr, env);

Formula translateExtFormula(nonEmpty(Expr expr), Environment env) 			
	= (\false() | \or(it,  m[x]) | Index x <- m, /relTheory() := x)
	when Binding m := translateExtExpr(expr, env);

Formula translateExtFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env) 
	= m == () ? \false() : (\true() | \and(it, m[x]) | Index x <- m, /relTheory() := x)
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
	= \and({\or({\not(m[x]), translateExtFormula(f, env + (hd.name:getSingletonBinding(x)))}) | Index x <- m, /relTheory() := x, Formula f := (([] == t) ? form : universal(t, form))})
	when [VarDeclaration hd, *t] := decls,
	     Binding m := translateExtExpr(hd.binding, env);

Formula translateExtFormula(existential(list[VarDeclaration] decls, Formula form), Environment env)
	= \or({\and({m[x], translateExtFormula(f, env + (hd.name: getSingletonBinding(x) + (<a,intTheory()>:m[<a,intTheory()>])))}) | Index x:<Atom a, relTheory()> <- m, Formula f := (([] == t) ? form : existential(t, form)), bprintln("name: <hd.name>, val <a>")}) 
	when [VarDeclaration hd, *t] := decls,
	     Binding m := translateExtExpr(hd.binding, env);

Formula translateExtFormula(gt(Expr lhsExpr, Expr rhsExpr), Environment env) 
	= (\true() | \and(it, \or(not(m[idx]), iM[idx2])) | Index idx:<Atom a, Atom b, relTheory()> <- m, Index idx2:<a, b, intTheory()> <- iM)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env),
		 arity(lhs) == 1 && arity(rhs) == 1,
		 Binding m := product(lhs, rhs),
		 Binding iM := (<a,b,intTheory()>:gt(lhs[<a, intTheory()>],rhs[<b, intTheory()>]) | <Atom a, intTheory()> <- lhs, <Atom b, intTheory()> <- rhs);

Formula translateExtFormula(gte(Expr lhsExpr, Expr rhsExpr), Environment env) 
	= (\true() | \and(it, \or(not(m[idx]), iM[idx2])) | Index idx:<Atom a, Atom b, relTheory()> <- m, Index idx2:<a, b, intTheory()> <- iM)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env),
		 arity(lhs) == 1 && arity(rhs) == 1,
		 Binding m := product(lhs, rhs),
		 Binding iM := (<a,b,intTheory()>:gte(lhs[<a, intTheory()>],rhs[<b, intTheory()>]) | <Atom a, intTheory()> <- lhs, <Atom b, intTheory()> <- rhs);

Formula translateExtFormula(lt(Expr lhsExpr, Expr rhsExpr), Environment env) 
	= (\true() | \and(it, \or(not(m[idx]), iM[idx2])) | Index idx:<Atom a, Atom b, relTheory()> <- m, Index idx2:<a, b, intTheory()> <- iM)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env),
		 arity(lhs) == 1 && arity(rhs) == 1,
		 Binding m := product(lhs, rhs),
		 Binding iM := (<a,b,intTheory()>:lt(lhs[<a, intTheory()>],rhs[<b, intTheory()>]) | <Atom a, intTheory()> <- lhs, <Atom b, intTheory()> <- rhs);

Formula translateExtFormula(lte(Expr lhsExpr, Expr rhsExpr), Environment env) 
	= (\true() | \and(it, \or(not(m[idx]), iM[idx2])) | Index idx:<Atom a, Atom b, relTheory()> <- m, Index idx2:<a, b, intTheory()> <- iM)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env),
		 arity(lhs) == 1 && arity(rhs) == 1,
		 Binding m := product(lhs, rhs),
		 Binding iM := (<a,b,intTheory()>:lte(lhs[<a, intTheory()>],rhs[<b, intTheory()>]) | <Atom a, intTheory()> <- lhs, <Atom b, intTheory()> <- rhs); 

Formula translateExtFormula(intEqual(Expr lhsExpr, Expr rhsExpr), Environment env) 
	= (\true() | \and(it, \or(not(m[idx]), iM[idx2])) | Index idx:<Atom a, Atom b, relTheory()> <- m, Index idx2:<a, b, intTheory()> <- iM)
	when map[str, Binding] r := (n:env[n] | n <- env, /_|Side/ !:= n),
		 bprintln(r),
		 Binding lhs := translateExtExpr(lhsExpr, env),
		 bprintln("lhs = <lhs>"),
		 Binding rhs := translateExtExpr(rhsExpr, env),
		 bprintln("rhs = <rhs>"),
		 arity(lhs) == 1 && arity(rhs) == 1,
		 Binding m := product(lhs, rhs), //(idx:val | Index idx:<Atom _, relTheory()> <- lhs, Formula val := (idx in rhs ? \and(lhs[idx],rhs[idx]) : lhs[idx])), 
		 Binding iM := (<a,b,intTheory()>:equal(lhs[<a, intTheory()>],rhs[<b, intTheory()>]) | <Atom a, intTheory()> <- lhs, <Atom b, intTheory()> <- rhs);

default Formula translateExtFormula(Formula f, Environment env) { throw "Translation of extended formula \'<f>\' not yet implemented";}

Binding translateExtExpr(variable(str name), Environment env) = env[name];

Binding translateExtExpr(transpose(Expr expr), Environment env) = transpose(m)
	when Binding m := translateExtExpr(expr, env); 

Binding translateExtExpr(closure(Expr expr), Environment env) = square(m, 1)
	when Binding m := translateExtExpr(expr, env);
		 
Binding translateExtExpr(reflexClosure(Expr expr), Environment env) = \or(m, env["_binId"])  
	when Binding m := translateExtExpr(closure(expr), env);
		
Binding translateExtExpr(\join(Expr lhsExpr, Expr rhsExpr), Environment env) = \join(lhs, rhs) 
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);
		
Binding translateExtExpr(product(Expr lhsExpr, Expr rhsExpr), Environment env) = product(lhs, rhs)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);

Binding translateExtExpr(ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr), Environment env)
	 = (idx:ite(translateExtFormula(caseForm, env),p[idx],q[idx]) | Index idx <- p, /relTheory() := idx)
	when Binding p := translateExtExpr(thenExpr, env),
		 Binding q := translateExtExpr(elseExpr, env);
		 
Binding translateExtExpr(comprehension(list[VarDeclaration] decls, Formula form), Environment env) {
	Index flatten([<Atom a, relTheory()>]) = <a, relTheory()>;
	Index flatten([<Atom a, relTheory()>, <Atom b, relTheory()>]) = <a,b, relTheory()>;
	Index flatten([<Atom a, relTheory()>, <Atom b, relTheory()>, <Atom c, relTheory()>]) = <a,b,c, relTheory()>;
	default Index flatten(list[Index] l) { throw "Unable to flatten a list of indices with an arity larger then 3"; }
	 
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

Binding translateExtExpr(union(Expr lhsExpr, Expr rhsExpr), Environment env) = \or(lhs,rhs) + (idx:lhs[idx] | Index idx:<Atom _, intTheory()> <- lhs) + (idx:rhs[idx] | Index idx:<Atom _, intTheory()> <- rhs)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);


Binding translateExtExpr(intersection(Expr lhsExpr, Expr rhsExpr), Environment env) = \and(lhs, rhs) +
	(idx:lhs[idx] | Index idx:<Atom _, intTheory()> <- lhs)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);		

Binding translateExtExpr(difference(Expr lhsExpr, Expr rhsExpr), Environment env) = 
	(x:\and(lhs[x],rhsVal) | Index x <- lhs, /relTheory() := x, Formula rhsVal := ((x notin rhs) ? \true() : \not(rhs[x]))) +
	(idx:lhs[idx] | Index idx:<Atom _, intTheory()> <- lhs)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);		

//Binding translateExtFormulaExpr(e:\join(Expr lhsExpr, Expr rhsExpr), Environment env) = translateExtExpr(e,env);
//Binding translateExtFormulaExpr(e:product(Expr lhsExpr, Expr rhsExpr), Environment env) = translateExtExpr(e,env);
//Binding translateExtFormulaExpr(e:ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr), Environment env) = translateExtExpr(e,env);
//Binding translateExtFormulaExpr(e:comprehension(list[VarDeclaration] decls, Formula form), Environment env) = translateExtExpr(e,env);

@memo
Binding translateExtExpr(intLit(int i), Environment env) = (<a, intTheory()>:\int(i) | <Atom a, Theory _> <- env["_emptyUnary"]) + (<a, relTheory()>:\true() | <Atom a, Theory _> <- env["_emptyUnary"]);

Binding translateExtExpr(multiplication(Expr lhsExpr, Expr rhsExpr), Environment env) = multiply(lhs, rhs)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);

Binding translateExtExpr(division(Expr lhsExpr, Expr rhsExpr), Environment env) = divide(lhs, rhs)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);

Binding translateExtExpr(addition(Expr lhsExpr, Expr rhsExpr), Environment env) = add(lhs, rhs)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);
		 
Binding translateExtExpr(subtraction(Expr lhsExpr, Expr rhsExpr), Environment env) = substract(lhs, rhs)
	when Binding lhs := translateExtExpr(lhsExpr, env),
		 Binding rhs := translateExtExpr(rhsExpr, env);

default Binding translateExtExpr(Expr e, Environment env) { throw "Translation of extended expression \'<e>\' not yet implemented";}

