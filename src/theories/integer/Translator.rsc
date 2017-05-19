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
 
TheoryFormula constructTheoryFormula(str relName, Formula relForm, atomAndTheory(Atom a, intTheory())) = form(relForm, equal(intVar("<relName>_<a>_int"), intVar("<a>")));
TheoryFormula constructTheoryFormula(str relName, Formula relForm, atomTheoryAndValue(Atom a, intTheory(), intVal(int i))) = form(relForm, equal(intVar("<relName>_<a>_int"), \int(i)));

Formula translateFormula(gt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return gt(l, r);})
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);

Formula translateFormula(gte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return gte(l, r);})
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);

Formula translateFormula(lt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return lt(l, r);})
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);
       
Formula translateFormula(lte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return lte(l, r);})
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);
       
Formula translateFormula(intEqual(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return equal(l, r);}) 
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni);

Formula translateFormula(intInequal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni) = translateFormula(negation(intEqual(lhsExpr, rhsExpr)), env, uni);

Formula translateFormula(RelationMatrix lhs, RelationMatrix rhs, Formula (Formula lhsElement, Formula rhsElement) operation) {
  if (arity(lhs) != 1 || arity(rhs) != 1) {
    throw "Unable to perform an integer equation on non-unary relations";
  }
  
  Formula result = \true();
  
  for(Index lhsIdx <- lhs, Index rhsIdx <- rhs) {
    if (0 notin lhs[lhsIdx].ext || 0 notin rhs[rhsIdx].ext) {
      throw "Can not perform an integer equation on relations that do not capture integer constraints";
    }
        
    for (form(Formula lhsRelForm, l:equal(lhsIntVar:intVar(str _), Formula _)) <- lhs[lhsIdx].ext[0], form(Formula rhsRelForm, r:equal(rhsIntVar:intVar(str _), Formula _)) <- rhs[rhsIdx].ext[0]) {
      result = \and(result, operation(lhsIntVar, rhsIntVar));
      result = \and(result,\if(lhsRelForm,l));
      result = \and(result,\if(rhsRelForm,r)); 
    } 
  }
  
  return result; 
}
       
@memo
RelationMatrix translateExpression(intLit(int i), Environment env, Universe uni) { throw "Int literal should have been removed from constraints by pre processing"; } 

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
  
  //for (Index idx <- m) {
  //  if (intTheory() notin m[idx].ext) { throw "Relation does not uniformly refer to integer variables"; }
  //  
  //  sumExpr = addition(\ite(m[idx].relForm, m[idx].ext[intTheory()][0], \int(0)), sumExpr);
  //} 
  
  return m; //translateIntConstant(sumExpr, env, uni);    
}
