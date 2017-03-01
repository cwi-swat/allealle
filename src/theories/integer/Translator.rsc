module theories::integer::Translator

extend theories::Translator;

import logic::Integer;
import logic::Boolean;

import theories::integer::Binder;
import theories::integer::AST;

import theories::relational::AST;
import theories::relational::Binder;
import theories::relational::Translator;

import List; 

import IO;
 
Binding createRelationalMapping(relationalBoundWithTheory(str relName, integers(), 1, list[Tuple] lb, list[Tuple] ub))
  = (<integers(), [a]>: intVar(a) | \tuple([Atom a]) <- ub) + createRelationalMapping(relationalBoundWithTheory(relName, relational(), 1, lb, ub));

Binding constructSingletonWithTheory(integers(), list[Atom] vector, Formula originalValue) = (<integers(),vector>:originalValue); 

Formula translateFormula(gt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) 
	= (\true() | \and(it, \or(not(relResult[relIdx]), intResult[intIdx])) | Index relIdx <- relResult, Index intIdx <- intResult)
	when Binding lhs := translateExpression(lhsExpr, env, uni),
		   Binding rhs := translateExpression(rhsExpr, env, uni),
		   Binding relResult := product(lhs, rhs),
		   Binding intResult := gt(lhs, rhs);

Formula translateFormula(gte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) 
	= (\true() | \and(it, \or(not(relResult[relIdx]), intResult[intIdx])) | Index relIdx <- relResult, Index intIdx <- intResult)
	when Binding lhs := translateExpression(lhsExpr, env, uni),
       Binding rhs := translateExpression(rhsExpr, env, uni),
       Binding relResult := product(lhs, rhs),
       Binding intResult := gte(lhs, rhs);

Formula translateFormula(lt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) 
  = (\true() | \and(it, \or(not(relResult[relIdx]), intResult[intIdx])) | Index relIdx <- relResult, Index intIdx <- intResult)
  when Binding lhs := translateExpression(lhsExpr, env, uni),
       Binding rhs := translateExpression(rhsExpr, env, uni),
       Binding relResult := product(lhs, rhs),
       Binding intResult := lt(lhs, rhs);
       
Formula translateFormula(lte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) 
  = (\true() | \and(it, \or(not(relResult[relIdx]), intResult[intIdx])) | Index relIdx <- relResult, Index intIdx <- intResult)
  when Binding lhs := translateExpression(lhsExpr, env, uni),
       Binding rhs := translateExpression(rhsExpr, env, uni),
       Binding relResult := product(lhs, rhs),
       Binding intResult := lte(lhs, rhs);
       
Formula translateFormula(intEqual(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) 
  = (\true() | \and(it, \or(not(relResult[relIdx]), intResult[intIdx])) | Index relIdx <- relResult, Index intIdx <- intResult)
  when Binding lhs := translateExpression(lhsExpr, env, uni),
       Binding rhs := translateExpression(rhsExpr, env, uni),
       Binding relResult := product(lhs, rhs),
       Binding intResult := equal(lhs, rhs);
       
@memo
Binding translateExpression(intLit(int i), Environment env, Universe uni) 
  = (<integers(),[a]>:\int(i) | Atom a <- uni.atoms) + (<relational(), [a]>:\true() | Atom a <- uni.atoms);

Binding translateExpression(multiplication(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = multiply(lhs, rhs) + product(lhs, rhs)
	when Binding lhs := translateExpression(lhsExpr, env, uni),
		   Binding rhs := translateExpression(rhsExpr, env, uni);

Binding translateExpression(division(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = divide(lhs, rhs) + product(lhs, rhs)
  when Binding lhs := translateExpression(lhsExpr, env, uni),
       Binding rhs := translateExpression(rhsExpr, env, uni);

Binding translateExpression(addition(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = add(lhs, rhs) + product(lhs, rhs)
  when Binding lhs := translateExpression(lhsExpr, env, uni),
       Binding rhs := translateExpression(rhsExpr, env, uni);
		 
Binding translateExpression(subtraction(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = substract(lhs, rhs) + product(lhs, rhs)
  when Binding lhs := translateExpression(lhsExpr, env, uni),
       Binding rhs := translateExpression(rhsExpr, env, uni);
