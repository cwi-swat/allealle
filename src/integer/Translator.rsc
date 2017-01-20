module integer::Translator

import Translator;

import logic::Integer;
import logic::Boolean;

import integer::Binder;
import integer::AST;

import relational::AST;
import relational::Binder;

import List; 

import IO;
 
Translator getIntTheoryTranslator() = translator(createInitialEnv, has, translateFormula, translateExpression, constructSingletonBinding);
  
Environment createInitialEnv(Problem p) 
  = (rb.relName:createRelationalMapping(rb) | RelationalBound rb <- p.bounds);

private Binding createRelationalMapping(relationalBoundWithTheory(str relName, integers(), 1, list[Tuple] lb, list[Tuple] ub))
  = (<integers(), [a]>: intVar(a) | \tuple([Atom a]) <- ub);

private default Binding createRelationalMapping(RelationalBound _) = ();


bool has(gt(Expr _, Expr _))              = true;
bool has(gte(Expr _, Expr _))             = true;
bool has(lt(Expr _, Expr _))              = true;
bool has(lte(Expr _, Expr _))             = true;
bool has(intEqual(Expr _, Expr _))        = true;
default bool has(AlleFormula _) = false; 

@memo
Environment constructSingletonBinding(str newVarName, Binding orig, list[Atom] vector) = (newVarName:(idx:orig[idx])) when Index idx:<integers(), vector> <- orig; 
@memo
default Environment constructSingletonBinding(str _, Binding _, list[Atom] _) = ();

Formula translateFormula(gt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) 
	= (\true() | \and(it, \or(not(relResult[relIdx]), intResult[intIdx])) | Index relIdx <- relResult, Index intIdx <- intResult)
	when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
		   Binding rhs := aggregate.translateExpression(rhsExpr, env, uni),
		   Binding relResult := product(lhs, rhs),
		   Binding intResult := gt(lhs, rhs);

Formula translateFormula(gte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) 
	= (\true() | \and(it, \or(not(relResult[relIdx]), intResult[intIdx])) | Index relIdx <- relResult, Index intIdx <- intResult)
	when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
       Binding rhs := aggregate.translateExpression(rhsExpr, env, uni),
       Binding relResult := product(lhs, rhs),
       Binding intResult := gte(lhs, rhs);

Formula translateFormula(lt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) 
  = (\true() | \and(it, \or(not(relResult[relIdx]), intResult[intIdx])) | Index relIdx <- relResult, Index intIdx <- intResult)
  when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
       Binding rhs := aggregate.translateExpression(rhsExpr, env, uni),
       Binding relResult := product(lhs, rhs),
       Binding intResult := lt(lhs, rhs);
       
Formula translateFormula(lte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) 
  = (\true() | \and(it, \or(not(relResult[relIdx]), intResult[intIdx])) | Index relIdx <- relResult, Index intIdx <- intResult)
  when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
       Binding rhs := aggregate.translateExpression(rhsExpr, env, uni),
       Binding relResult := product(lhs, rhs),
       Binding intResult := lte(lhs, rhs);
       
Formula translateFormula(intEqual(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) 
  = (\true() | \and(it, \or(not(relResult[relIdx]), intResult[intIdx])) | Index relIdx <- relResult, Index intIdx <- intResult)
  when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
       Binding rhs := aggregate.translateExpression(rhsExpr, env, uni),
       Binding relResult := product(lhs, rhs),
       Binding intResult := equal(lhs, rhs);
       
@memo
Binding translateExpression(intLit(int i), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) 
  = (<integers(),[a]>:\int(i) | Atom a <- uni.atoms) + (<relational(), [a]>:\true() | Atom a <- uni.atoms);

Binding translateExpression(multiplication(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = multiply(lhs, rhs) + product(lhs, rhs)
	when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
		   Binding rhs := aggregate.translateExpression(rhsExpr, env, uni);

Binding translateExpression(division(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = divide(lhs, rhs) + product(lhs, rhs)
  when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
       Binding rhs := aggregate.translateExpression(rhsExpr, env, uni);

Binding translateExpression(addition(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = add(lhs, rhs) + product(lhs, rhs)
  when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
       Binding rhs := aggregate.translateExpression(rhsExpr, env, uni);
		 
Binding translateExpression(subtraction(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = substract(lhs, rhs) + product(lhs, rhs)
  when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
       Binding rhs := aggregate.translateExpression(rhsExpr, env, uni);

default Binding translateExpression(Expr e, Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = ();
