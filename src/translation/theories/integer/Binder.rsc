module translation::theories::integer::Binder

extend translation::Binder;

import translation::theories::integer::AST;
import logic::Integer;

bool isIntForm(\int(int _)) = true;
bool isIntForm(intVar(str _)) = true;
default bool isIntForm(Formula _) = false; 
 
Formula toIntVar(Index idx, str attName) = intVar(toIntVarName(idx, attName));
str toIntVarName(Index idx, str attName) = "<intercalate("_", idx)>!<attName>";
 
@memo
RelationMatrix unary(RelationMatrix m, Formula (Formula) opr, AdditionalConstraintFunctions acf) {
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
RelationMatrix binary(RelationMatrix lhs, RelationMatrix rhs, Formula (Formula l, Formula r) opr, AdditionalConstraintFunctions acf) {
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
      throw "Can not perform integer arithmetic operation on non integer attributes";
    } 
  }

  return result;
}  

@memo 
RelationMatrix nary(list[RelationMatrix] terms, Formula (Formula lhs, Formula rhs) opr, Formula startAttForm, AdditionalConstraintFunctions acf) {
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
  
  RelationMatrix buildResult([RelationMatrix hd, *RelationMatrix tl], Formula relForm, Formula attForm) {
    RelationMatrix relResult = ();
    
    for (Index idx <- hd) {
      if (relAndAtt(Formula r, Formula a) := hd[idx], isIntForm(a)) {
        relResult += buildResult(tl, \and(relForm, hd[idx].relForm), opr(attForm, a));
      } else {
        throw "Can not perform integer arithmetic operation on non integer attributes";
      }
    }
    
    return relResult;
  }
  
  return buildResult(terms, \true(), startAttForm);
}

@memo
RelationMatrix sum(RelationMatrix m, AdditionalConstraintFunctions acf) {
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
RelationMatrix cardinality(RelationMatrix m, AdditionalConstraintFunctions acf) {
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


