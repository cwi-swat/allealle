module translation::theories::integer::Translator

extend translation::Translator;

import logic::Integer;
import logic::Boolean;

import translation::theories::integer::AST;
import translation::AST; 
import translation::Binder;
 
import List;   
import Set;
import Map;
import IO;
 
Formula createAttribute(Index idx, str name, \int(), hole()) = toIntVar(idx, name);  
Formula createAttribute(Index idx, str name, \int(), lit(posInt(int i))) = \int(i);  
Formula createAttribute(Index idx, str name, \int(), lit(negInt(int i))) = neg(\int(i));  

Formula toIntVar(Index idx, str attName) = intVar(toIntVarName(idx, attName));
str toIntVarName(Index idx, str attName) = "<intercalate("_", idx)>!<attName>";

@memo
Formula translateFormula(gt(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return gt(l, r);}, acf)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

@memo
Formula translateFormula(gte(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return gte(l, r);}, acf)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

@memo
Formula translateFormula(lt(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return lt(l, r);}, acf)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

@memo
Formula translateFormula(lte(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return lte(l, r);}, acf)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

@memo
Formula translateFormula(intEqual(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return equal(l, r);}, acf) 
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

@memo
Formula translateFormula(intInequal(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return inequal(l, r);}, acf) 
  when RelationMatrix lhs := translateExpression(lhsExpr, env, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, acf);

bool isIntForm(\int(int _)) = true;
bool isIntForm(intVar(str _)) = true;
default bool isIntForm(Formula _) = false; 

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

@memo
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

@memo
RelationMatrix translateExpression(intLit(int i), Environment env, AdditionalConstraintFunctions acf) = (["_c<i>"] : relAndAtt(\true(), \int(i))); 
  
@memo
RelationMatrix translateExpression(neg(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) 
  = translateUnaryExpression(expr, Formula (Formula f) { return neg(f); }, env, acf);

@memo
RelationMatrix translateExpression(abs(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) 
  = translateUnaryExpression(expr, Formula (Formula f) { return abs(f); }, env, acf);

private RelationMatrix translateUnaryExpression(AlleExpr expr, Formula (Formula) opr, Environment env, AdditionalConstraintFunctions acf) {
  RelationMatrix m = translateExpression(expr, env, acf);
  
  for (Index idx <- m) {
    if (relAndAtt(Formula relForm, Formula attForm) := m[idx], isIntForm(attForm)) {
      Index tmpIdx = [acf.freshIntermediateId()];
      Formula tmpVar = toIntVar(tmpIdx, "val");
      
      acf.addIntermediateVar(tmpVar);       
      acf.addAttributeConstraint(equal(tmpVar, opr(attForm)));
      
      m[idx] = relAndAtt(m[idx].relForm, tmpVar);      
    } else {
      throw "Can not negate integer attribute on a non selected integer attribute";
    }
  }
  
  return m;
}

@memo
RelationMatrix translateExpression(addition(list[AlleExpr] terms), Environment env, AdditionalConstraintFunctions acf)
  = translateNaryExpression(terms, Formula (Formula lhs, Formula rhs) { return addition(lhs, rhs); }, \int(0), env, acf);

@memo
RelationMatrix translateExpression(multiplication(list[AlleExpr] terms), Environment env, AdditionalConstraintFunctions acf) 
  = translateNaryExpression(terms, Formula (Formula lhs, Formula rhs) { return multiplication(lhs, rhs); }, \int(1), env, acf);


private RelationMatrix translateNaryExpression(list[AlleExpr] terms, Formula (Formula lhs, Formula rhs) opr, Formula startAttForm, Environment env, AdditionalConstraintFunctions acf) {
  RelationMatrix buildResult([], Formula relForm, Formula attForm) {
    Index tmpIdx = [acf.freshIntermediateId()];

    if (\int(_) := attForm) {
      return (tmpIdx: relAndAtt(relForm, attForm));
    } else {
      Formula tmpVar = toIntVar(tmpIdx, "val");

      acf.addIntermediateVar(tmpVar);       
      acf.addAttributeConstraint(equal(tmpVar, attForm));

      return (tmpIdx: relAndAtt(relForm, tmpVar));
    }
  }
  
  RelationMatrix buildResult([AlleExpr hd, *AlleExpr tl], Formula relForm, Formula attForm) {
    RelationMatrix m = translateExpression(hd, env, acf);
    
    RelationMatrix relResult = ();
    
    for (Index idx <- m) {
      if (relAndAtt(Formula r, Formula a) := m[idx], isIntForm(a)) {
        relResult += buildResult(tl, \and(relForm, m[idx].relForm), opr(attForm, a));
      } else {
        throw "Can not perform integer arithmetic operation on non integer attributes";
      }
    }
    
    return relResult;
  }
  
  return buildResult(terms, \true(), startAttForm);
}

@memo
RelationMatrix translateExpression(subtraction(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) 
  = translateBinaryExpression(lhsExpr, rhsExpr, Formula (Formula l, Formula r) {return addition(l,neg(r));}, env, acf);

@memo
RelationMatrix translateExpression(division(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) 
  = translateBinaryExpression(lhsExpr, rhsExpr, Formula (Formula l, Formula r) {return division(l,r);}, env, acf);

@memo
RelationMatrix translateExpression(modulo(AlleExpr lhsExpr, AlleExpr rhsExpr), Environment env, AdditionalConstraintFunctions acf) 
  = translateBinaryExpression(lhsExpr, rhsExpr, Formula (Formula l, Formula r) {return modulo(l,r);}, env, acf);

private RelationMatrix translateBinaryExpression(AlleExpr lhsExpr, AlleExpr rhsExpr, Formula (Formula l, Formula r) opr, Environment env, AdditionalConstraintFunctions acf) {
  RelationMatrix lhs = translateExpression(lhsExpr, env, acf);
  RelationMatrix rhs = translateExpression(rhsExpr, env, acf);
  
  if (lhs == () || rhs == ()) { 
    return ();
  }
  
  RelationMatrix result = ();
  
  for (Index lIdx <- lhs, lhs[lIdx].relForm != \false(), Index rIdx <- rhs, rhs[rIdx].relForm != \false()) {

    if (relAndAtt(Formula lhsRel, Formula lhsAtt) := lhs[lIdx], isIntForm(lhsAtt), 
        relAndAtt(Formula rhsRel, Formula rhsAtt) := rhs[rIdx], isIntForm(rhsAtt)) {       
      Formula opResult = opr(lhsAtt, rhsAtt);
      Index tmpIdx = [acf.freshIntermediateId()];       

      if (\int(_) := opResult) { 
        result[tmpIdx] = relAndAtt(\and(lhs[lIdx].relForm, rhs[rIdx].relForm), opResult);
      } else {
      
        Formula tmpVar = toIntVar(tmpIdx, "val");
      
        acf.addIntermediateVar(tmpVar);
        acf.addAttributeConstraint(equal(tmpVar, opResult));
        
        result[tmpIdx] = relAndAtt(\and(lhs[lIdx].relForm, rhs[rIdx].relForm), tmpVar);
      }
    } else {
      throw "Can not perform integer arithmetic operation on non  integer attributes";
    } 
  }

  return result;
}  

@memo
RelationMatrix translateExpression(sum(AlleExpr e), Environment env, AdditionalConstraintFunctions acf) {
  RelationMatrix m = translateExpression(e, env, acf);
  
  Index tmpIdx = [acf.freshIntermediateId()];
  Formula tmpVar = toIntVar(tmpIdx, "val");
  
  acf.addIntermediateVar(tmpVar);

  Formula attResult = \int(0);
  for (Index idx <- m) {
    if (relAndAtt(Formula r, Formula a) := m[idx], isIntForm(a)) {
      attResult = addition(attResult, ite(r, a, \int(0)));
    } else {
      throw "Can not perform sum on non selected integer attributes";
    } 
  }
  
  acf.addAttributeConstraint(equal(tmpVar, attResult));
  
  return (tmpIdx : relAndAtt(\true(), tmpVar));   
}

@memo
RelationMatrix translateExpression(car(AlleExpr e), Environment env, AdditionalConstraintFunctions acf) {
  RelationMatrix m = translateExpression(e, env, acf);

  Index tmpIdx = [acf.freshIntermediateId()];
  Formula tmpVar = toIntVar(tmpIdx, "val");
  
  acf.addIntermediateVar(tmpVar);
  
  Formula attResult = \int(0);
  for (Index idx <- m) {
    attResult = addition(attResult, ite(m[idx].relForm, \int(1), \int(0)));
  }
  
  acf.addAttributeConstraint(equal(tmpVar, attResult));
  
  return (tmpIdx : relAndAtt(\true(), tmpVar));   
}
