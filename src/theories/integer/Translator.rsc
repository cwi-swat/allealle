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
TheoryFormula constructTheoryFormula(str relName, Formula relForm, atomTheoryAndValue(Atom a, intTheory(), intExpr(Expr expr))) = form(relForm, equal(intVar("<relName>_<a>_int"), f))
  when f:\int(int i) := exprToForm(expr);
   
TheoryFormula constructTheoryFormula(str relName, Formula relForm, atomTheoryAndValue(Atom a, intTheory(), intExpr(Expr expr))) = form(relForm, equal(intVar("<relName>_<a>_int"), intVar("<a>")))
  when \int(int _) !:= exprToForm(expr);

Formula exprToForm(intLit(int i))                       = \int(i);
Formula exprToForm(neg(Expr e))                         = neg(exprToForm(e));
Formula exprToForm(variable(str v))                     = var(v);
Formula exprToForm(multiplication(Expr lhs, Expr rhs))  = multiplication(exprToForm(lhs), exprToForm(rhs));
Formula exprToForm(division(Expr lhs, Expr rhs))        = division(exprToForm(lhs), exprToForm(rhs));
Formula exprToForm(modulo(Expr lhs, Expr rhs))          = modulo(exprToForm(lhs), exprToForm(rhs));
Formula exprToForm(addition(Expr lhs, Expr rhs))        = addition(exprToForm(lhs), exprToForm(rhs));
Formula exprToForm(subtraction(Expr lhs, Expr rhs))     = substraction(exprToForm(lhs), exprToForm(rhs));

Formula translateFormula(gt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return gt(l, r);}, addTheoryConstraint)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint);

Formula translateFormula(gte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return gte(l, r);}, addTheoryConstraint)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint);

Formula translateFormula(lt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return lt(l, r);}, addTheoryConstraint)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint);
       
Formula translateFormula(lte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return lte(l, r);}, addTheoryConstraint)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint);
       
Formula translateFormula(intEqual(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return equal(l, r);}, addTheoryConstraint) 
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint);

Formula translateFormula(intInequal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return inequal(l, r);}, addTheoryConstraint) 
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint);

Formula translateFormula(RelationMatrix lhs, RelationMatrix rhs, Formula (Formula lhsElement, Formula rhsElement) operation, void (set[TheoryFormula]) addTheoryConstraint) {
  if (arity(lhs) == 0 || arity(rhs) == 0) { return \true(); }
  
  if (arity(lhs) != 1 || arity(rhs) != 1) {
    println(lhs); println(rhs);
    throw "Unable to perform an integer equation on non-unary relations";
  }
  
  Formula result = \true();
  
  for(Index lhsIdx <- lhs) {
    set[Formula] ors = {};

    for (Index rhsIdx <- rhs) {
      if (0 notin lhs[lhsIdx].ext || 0 notin rhs[rhsIdx].ext) {
        throw "Can not perform an integer equation on relations that do not capture integer constraints";
      }
      
      Formula tmpResult = \true();   
         
      for (l:form(Formula lhsRelForm, equal(lhsIntVar:intVar(str _), Formula _)) <- lhs[lhsIdx].ext[0], r:form(Formula rhsRelForm, equal(rhsIntVar:intVar(str _), Formula _)) <- rhs[rhsIdx].ext[0]) {
        tmpResult = \and(tmpResult, operation(lhsIntVar, rhsIntVar));
        
        addTheoryConstraint({l});
        addTheoryConstraint({r}); 
      }
      
      ors += \or(\not(rhs[rhsIdx].relForm), tmpResult); 
    }

    result = \and(result, \or(\not(lhs[lhsIdx].relForm), \and(ors)));
  }    
  
  return result; 
}
       
@memo
RelationMatrix translateExpression(intLit(int i), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) { throw "Int literal should have been removed from constraints by pre processing"; } 

//RelationMatrix translateExpression(multiplication(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) = multiply(lhs, rhs)
//	when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint),
//		   RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint);
//
//RelationMatrix translateExpression(division(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) = divide(lhs, rhs)
//  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint),
//       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint);
//
//RelationMatrix translateExpression(modulo(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) = modd(lhs, rhs)
//  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint),
//       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint);
//
//RelationMatrix translateExpression(addition(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) = add(lhs, rhs)
//  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint),
//       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint);
//		 
//RelationMatrix translateExpression(subtraction(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) = substract(lhs, rhs)
//  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, addTheoryConstraint),
//       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, addTheoryConstraint);
//       
//RelationMatrix translateExpression(sum(list[VarDeclaration] decls, Expr expr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint) {
//  
//  RelationMatrix m = translateExpression(decls[0].binding, env, uni, addTheoryConstraint);
//  
//  Formula sumExpr = \int(0);
//  
//  //for (Index idx <- m) {
//  //  if (intTheory() notin m[idx].ext) { throw "Relation does not uniformly refer to integer variables"; }
//  //  
//  //  sumExpr = addition(\ite(m[idx].relForm, m[idx].ext[intTheory()][0], \int(0)), sumExpr);
//  //} 
//  
//  return m; //translateIntConstant(sumExpr, env, uni);    
//}
