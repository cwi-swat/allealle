module extended::Translator

extend orig::Translator;

import logic::Integer;

data Theory = intTheory();

Environment createRelationalMapping(relationalBound(str relName, intSort(), 1, list[Tuple] lb, list[Tuple] ub)) 
	= (relName:(<a, intTheory()>:"<relName>_<a>" | \tuple([Atom a]) <- ub)) + 
	  createRelationalMapping(relationalBound(relName, arity, lb, ub)); 

default Environment createRelationalMapping(relationalBound(str relName, Sort s, int arity, list[Tuple] _, list[Tuple] _))
	{throw "Unable to create initial binding for relation <relName> of sort <s> with arity <arity>";}

@memo	
Binding translateExpr(intLit(int i), Environment env) = (idx:intVal(i) | Index idx <- env["_emptyUnary"]);

Binding translateExpr(multiplication(Expr lhsExpr, Expr rhsExpr), Environment env) = multiply(lhs, rhs)
	when Binding lhs := translateExpr(lhs, env),
		 Binding rhs := translateExpr(rhs, env);

	//| division(Expr lhs, Expr rhs)
	//| addition(Expr lhs, Expr rhs)
	//| subtraction(Expr lhs, Expr rhs)
