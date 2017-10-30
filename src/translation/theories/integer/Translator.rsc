module translation::theories::integer::Translator

extend translation::Translator;

import logic::Integer;
import logic::Boolean;

import translation::theories::integer::AST;
import translation::theories::integer::Binder;
import translation::AST; 
 
import List;   
import Set;
import Map;
import IO;

Formula translateFormula(gt(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return gt(l, r);}, acf)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

Formula translateFormula(gte(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return gte(l, r);}, acf)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

Formula translateFormula(lt(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return lt(l, r);}, acf)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

Formula translateFormula(lte(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return lte(l, r);}, acf)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

Formula translateFormula(intEqual(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return equal(l, r);}, acf) 
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

Formula translateFormula(intInequal(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return inequal(l, r);}, acf) 
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

@memo
Formula translateIntCompFormula(RelationMatrix lhs, RelationMatrix rhs, Formula (Formula lhsElement, Formula rhsElement) operation, AdditionalConstraintFunctions acf) {
  if (size(lhs) == 0 || size(rhs) == 0) { return \false(); }
    
  Formula result = \true();

  for(Index lhsIdx <- lhs) {
    if (relAndAtt(Formula _, Formula lhsAtt) !:= lhs[lhsIdx], !isIntForm(lhsAtt)) {
      throw "Can not perform an integer equation on non integer attributes";
    }
    
    set[Formula] ors = {};
 
    for (Index rhsIdx <- rhs) {
      if (relAndAtt(Formula _, Formula rhsAtt) !:= rhs[rhsIdx], !isIntForm(rhsAtt)) {
        throw "Can not perform an integer equation on non integer attributes";
      }

      ors += \or(\not(lhs[lhsIdx].relForm), \or(\not(rhs[rhsIdx].relForm), operation(lhs[lhsIdx].attForm, rhs[rhsIdx].attForm))); 
    }

    result = \and(result, \and(ors));
  }    
  
  return result; 
} 

Formula translateFormula(distinct(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) {
  RelationMatrix m = translateExpression(expr, env, acf);
   
  list[Formula] terms = [];
  for (Index idx <- m) {
    if (relAndAtt(Formula relForm, Formula attForm) := m[idx], isIntForm(attForm)) {
      Index tmpIdx = [acf.freshIntermediateId()];
      Formula tmpVar = toIntVar(tmpIdx, "val");
      acf.addIntermediateVar(tmpVar);       
      
      terms += ite(relForm, attForm, tmpVar);
    } else {
      throw "Can not perform integer distinct on non integer attribute";
    }
  } 
  
  return distinct(terms);
}       

RelationMatrix translateExpression(intLit(int i), Environment env, AdditionalConstraintFunctions acf) = (["_c<i>"] : relAndAtt(\true(), \int(i))); 
  
RelationMatrix translateExpression(neg(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) = unary(m, Formula (Formula f) { return neg(f); }, acf)
  when RelationMatrix m := translateExpression(expr, env, acf);

RelationMatrix translateExpression(abs(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) = unary(m, Formula (Formula f) { return abs(f); }, acf)
  when RelationMatrix m := translateExpression(expr, env, acf);

RelationMatrix translateExpression(addition(list[AlleExpr] termExprs), Environment env, AdditionalConstraintFunctions acf) = nary(terms, Formula (Formula lhs, Formula rhs) { return addition(lhs, rhs); }, \int(0), acf)
  when list[RelationMatrix] terms := [translateExpression(t, env, acf) | AlleExpr t <- termExprs];  

RelationMatrix translateExpression(multiplication(list[AlleExpr] termExprs), Environment env, AdditionalConstraintFunctions acf) = nary(terms, Formula (Formula lhs, Formula rhs) { return multiplication(lhs, rhs); }, \int(1), acf)
  when list[RelationMatrix] terms := [translateExpression(t, env, acf) | AlleExpr t <- termExprs];

RelationMatrix translateExpression(subtraction(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = binary(lhs, rhs, Formula (Formula l, Formula r) {return addition(l,neg(r));}, acf)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);
 
RelationMatrix translateExpression(division(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = binary(lhs, rhs, Formula (Formula l, Formula r) {return division(l,r);}, acf)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

RelationMatrix translateExpression(modulo(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = binary(lhs, rhs, Formula (Formula l, Formula r) {return modulo(l,r);}, acf)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

RelationMatrix translateExpression(sum(AlleExpr e), Environment env, AdditionalConstraintFunctions acf) = sum(m, acf)
  when RelationMatrix m := translateExpression(e, env, acf);

RelationMatrix translateExpression(car(AlleExpr e), Environment env, AdditionalConstraintFunctions acf) = cardinality(m, acf)
  when RelationMatrix m := translateExpression(e, env, acf);