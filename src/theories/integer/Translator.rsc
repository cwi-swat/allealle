module theories::integer::Translator

extend theories::Translator;

import logic::Integer;
import logic::Boolean;

import theories::integer::Binder;
import theories::integer::AST;

import theories::AST; 
import theories::Binder;
import theories::Translator;
 
import List;  
 
import IO;
 
ExtensionEncoding constructTheoryExtension(int idx, atomAndTheory(Atom a, intTheory())) = (idx : \intVar(a));
ExtensionEncoding constructTheoryExtension(int idx, atomTheoryAndValue(Atom a, intTheory(), intVal(int i))) = (idx:\int(i));

Formula translateFormula(gt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateFormula(result)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni),
       RelationMatrix result := gt(lhs, rhs);

Formula translateFormula(gte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateFormula(result)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni),
       RelationMatrix result := gte(lhs, rhs);

Formula translateFormula(lt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateFormula(result)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni),
       RelationMatrix result := lt(lhs, rhs);
       
Formula translateFormula(lte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateFormula(result)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni),
       RelationMatrix result := lte(lhs, rhs);
       
Formula translateFormula(intEqual(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = formResult 
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni),
       RelationMatrix result := equal(lhs, rhs),
       Formula formResult := translateFormula(result);

Formula translateFormula(intInequal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateFormula(negation(intEqual(lhsExpr, rhsExpr)), env, uni);

private Formula translateFormula(RelationMatrix operationResult) 
  = (\true() | \and(it, \or(\not(operationResult[idx].relForm), (\true() | \and(it, enc[i]) | ExtensionEncoding enc := operationResult[idx].ext[intTheory()], int i <- enc))) | Index idx <- operationResult, intTheory() in operationResult[idx].ext);
       
@memo
RelationMatrix translateExpression(intLit(int i), Environment env, Universe uni) = translateIntConstant(\int(i), env, uni); 

private RelationMatrix translateIntConstant(Formula f, Environment env, Universe uni)
  = ([a]:<\true(), (intTheory():(0:f))> | AtomDecl ad <- uni.atoms, atomAndTheory(Atom a, intTheory()) := ad || atomTheoryAndValue(Atom a, intTheory(), intVal(int _)) := ad);

RelationMatrix translateExpression(multiplication(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = multiply(lhs, rhs)
	when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
		   RelationMatrix rhs := translateExpression(rhsExpr, env, uni);

RelationMatrix translateExpression(division(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = divide(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);

RelationMatrix translateExpression(modulo(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = modd(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);

RelationMatrix translateExpression(addition(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = add(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);
		 
RelationMatrix translateExpression(subtraction(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = substract(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);
       
RelationMatrix translateExpression(sum(list[VarDeclaration] decls, Expr expr), Environment env, Universe uni) {
  
  RelationMatrix m = translateExpression(decls[0].binding, env, uni);
  
  Formula sumExpr = \int(0);
  
  for (Index idx <- m) {
    if (intTheory() notin m[idx].ext) { throw "Relation does not uniformly refer to integer variables"; }
    
    sumExpr = addition(\ite(m[idx].relForm, m[idx].ext[intTheory()][0], \int(0)), sumExpr);
  } 
  
  return translateIntConstant(sumExpr, env, uni);    
}

bool contains(TheoryExtension ext, str varName, intTheory()) = /intVar(varName) := ext;
