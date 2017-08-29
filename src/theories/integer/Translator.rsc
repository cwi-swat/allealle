module theories::integer::Translator

extend theories::Translator;

import logic::Integer;
import logic::Boolean;

import theories::integer::AST;

import theories::AST; 
import theories::Binder;
import theories::Translator;
 
import List;  
import Set;
import Map;
 
import IO;
 
Formula constructAttribute(Atom a, attribute(str name, intTheory())) = toIntVar(a,name);
Formula constructAttribute(Atom a, attributeAndValue(str name, intTheory(), intExpr(Expr expr))) {
  Formula attForm = exprToForm(expr);
 
  if (\int(int i) := attForm) {
    return attForm;
  } else {
    return toIntVar(a, name);
  }
}

Formula exprToForm(intLit(int i))                              = \int(i);
Formula exprToForm(neg(Expr e))                                = neg(exprToForm(e));
Formula exprToForm(attributeLookup(variable(str v), str name)) = var("<v>!<name>"); 
Formula exprToForm(multiplication(list[Expr] terms))           = multiplication([exprToForm(t) | Expr t <- terms]);
Formula exprToForm(division(Expr lhs, Expr rhs))               = division(exprToForm(lhs), exprToForm(rhs));
Formula exprToForm(modulo(Expr lhs, Expr rhs))                 = modulo(exprToForm(lhs), exprToForm(rhs));
Formula exprToForm(addition(list[Expr] terms))                 = addition([exprToForm(t) | Expr t <- terms]);
Formula exprToForm(subtraction(Expr lhs, Expr rhs))            = substraction(exprToForm(lhs), exprToForm(rhs));

Formula toIntVar(str atom, str attName) = intVar(toIntVarName(atom, attName));
str toIntVarName(str atom, str attName) = "<atom>!<attName>";

Formula translateFormula(gt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return gt(l, r);}, acf, cache)
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, uni, acf, cache),
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, uni, acf, cache);

Formula translateFormula(gte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return gte(l, r);}, acf, cache)
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, uni, acf, cache),
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, uni, acf, cache);

Formula translateFormula(lt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return lt(l, r);}, acf, cache)
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, uni, acf, cache),
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, uni, acf, cache);

Formula translateFormula(lte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return lte(l, r);}, acf, cache)
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, uni, acf, cache),
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, uni, acf, cache);

Formula translateFormula(intEqual(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return equal(l, r);}, acf, cache) 
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, uni, acf, cache),
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, uni, acf, cache);

Formula translateFormula(intInequal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) = translateIntCompFormula(lhs, rhs, Formula (Formula l, Formula r) { return inequal(l, r);}, acf, cache) 
  when RelationMatrix lhs := translateCachedExpression(lhsExpr, env, uni, acf, cache),
       RelationMatrix rhs := translateCachedExpression(rhsExpr, env, uni, acf, cache);

Formula translateIntCompFormula(RelationMatrix lhs, RelationMatrix rhs, Formula (Formula lhsElement, Formula rhsElement) operation, AdditionalConstraintFunctions acf, Cache cache) {
  if (arity(lhs) == 0 || arity(rhs) == 0) { return \false(); }
  
  if (arity(lhs) != 1 || arity(rhs) != 1) {
    throw "Unable to perform an integer equation on non-unary relations";
  }
  
  Formula result = \true();
  
  for(Index lhsIdx <- lhs) {
    if (relAndAtt(Formula _, Formula lhsAtt) !:= lhs[lhsIdx], \int(_) !:= lhsAtt && intVar(_) !:= lhsAtt) {
      throw "Can not perform an integer equation on unary relations with selected integer attributes";
    }
    
    set[Formula] ors = {};
 
    for (Index rhsIdx <- rhs) {
      if (relAndAtt(Formula _, Formula rhsAtt) !:= rhs[rhsIdx], \int(_) !:= rhsAtt && intVar(_) !:= rhsAtt) {
        throw "Can not perform an integer equation on unary relations with selected integer attributes";
      }

      ors += \or(\not(lhs[lhsIdx].relForm), \or(\not(rhs[rhsIdx].relForm), operation(lhs[lhsIdx].attForm, rhs[rhsIdx].attForm))); 
    }

    result = \and(result, \and(ors));
  }    
  
  return result; 
}       

RelationMatrix translateExpression(intLit(int i), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  Atom consAtom = "_c<i>";
  
  acf.addAtomToUniverse(atomWithAttributes(consAtom, [attributeAndValue("cons", intTheory(), intExpr(intLit(i)))]));
  
  return (["_c<i>"] : relAndAtt(\true(), \int(i))); 
}
  
RelationMatrix translateExpression(neg(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix m = translateCachedExpression(expr, env, uni, acf, cache);
  
  for (Index idx <- m) {
    if (relAndAtt(Formula relForm, Formula attForm) := m[idx], \int(_) := attForm || intVar(_) := attForm) {
      Atom resultAtom = acf.freshAtom();       
      acf.addAtomToUniverse(atomWithAttributes(resultAtom, [attribute("val", intTheory())]));  
      acf.addAttributeConstraint(equal(toIntVar(resultAtom,"val"), neg(attForm)));
      
      m[idx] = relAndAtt(m[idx].relForm, toIntVar(resultAtom, "val"));      
    } else {
      throw "Can not negate integer attribute on a non selected integer attribute";
    }
  }
  
  return m;
}

RelationMatrix translateExpression(abs(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix m = translateCachedExpression(expr, env, uni, acf, cache);
  
  for (Index idx <- m) {
    if (relAndAtt(Formula relForm, Formula attForm) := m[idx], \int(_) := attForm || intVar(_) := attForm) {
      Atom resultAtom = acf.freshAtom();       
      acf.addAtomToUniverse(atomWithAttributes(resultAtom, [attribute("val", intTheory())]));  
      acf.addAttributeConstraint(equal(toIntVar(resultAtom,"val"), abs(attForm)));
      
      m[idx] = relAndAtt(m[idx].relForm, toIntVar(resultAtom, "val"));      
    } else {
      throw "Can not negate integer attribute on a non selected integer attribute";
    }
  }
  
  return m;
}

RelationMatrix translateExpression(addition(list[Expr] terms), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache)
  = translateExpression(terms, Formula (Formula lhs, Formula rhs) { return addition(lhs, rhs); }, \int(0), env, uni, acf, cache);

RelationMatrix translateExpression(multiplication(list[Expr] terms), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) 
  = translateExpression(terms, Formula (Formula lhs, Formula rhs) { return multiplication(lhs, rhs); }, \int(1), env, uni, acf, cache);


private RelationMatrix translateExpression(list[Expr] terms, Formula (Formula lhs, Formula rhs) operation, Formula startAttForm, Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix buildResult([], Formula relForm, Formula attForm) {
    Atom resultAtom = acf.freshAtom();

    if (\int(_) := attForm) {
      return ([resultAtom]: relAndAtt(relForm, attForm));
    } else {
      acf.addAtomToUniverse(atomWithAttributes(resultAtom, [attribute("val", intTheory())]));
      acf.addAttributeConstraint(equal(toIntVar(resultAtom, "val"), attForm));

      return ([resultAtom]: relAndAtt(relForm, toIntVar(resultAtom, "val")));
    }
  }
  
  RelationMatrix buildResult([Expr hd, *Expr tl], Formula relForm, Formula attForm) {
    RelationMatrix m = translateCachedExpression(hd, env, uni, acf, cache);
    
    RelationMatrix relResult = ();
    
    for (Index idx <- m) {
      if (relAndAtt(Formula r, Formula a) := m[idx], \int(_) := a || intVar(_) := a) {
        relResult += buildResult(tl, \and(relForm, m[idx].relForm), operation(attForm, a));
      } else {
        throw "Can not perform integer arithmetic operation on non selected integer attributes";
      }
    }
    
    return relResult;
  }
  
  return buildResult(terms, \true(), startAttForm);
}

RelationMatrix translateExpression(subtraction(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) 
  = translateExpression(lhsExpr, rhsExpr, Formula (Formula l, Formula r) {return addition(l,neg(r));}, env, uni, acf, cache);

RelationMatrix translateExpression(division(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) 
  = translateExpression(lhsExpr, rhsExpr, Formula (Formula l, Formula r) {return division(l,r);}, env, uni, acf, cache);

RelationMatrix translateExpression(modulo(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) 
  = translateExpression(lhsExpr, rhsExpr, Formula (Formula l, Formula r) {return modulo(l,r);}, env, uni, acf, cache);

private RelationMatrix translateExpression(Expr lhsExpr, Expr rhsExpr, Formula (Formula l, Formula r) operation, Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix lhs = translateCachedExpression(lhsExpr, env, uni, acf, cache);
  RelationMatrix rhs = translateCachedExpression(rhsExpr, env, uni, acf, cache);
  
  if (lhs == () || rhs == ()) { 
    return ();
  }
  
  if (size(getOneFrom(lhs)) != 1 || size(getOneFrom(rhs)) != 1) {
    throw "Can only perform binary integer arithmetic of unary base relations";
  } 
  
  RelationMatrix relResult = ();
  
  for (Index lIdx <- lhs, lhs[lIdx].relForm != \false(), Index rIdx <- rhs, rhs[rIdx].relForm != \false()) {
    
    if (relAndAtt(Formula lhsRel, Formula lhsAtt) := lhs[lIdx], \int(_) := lhsAtt || intVar(_) := lhsAtt, 
        relAndAtt(Formula rhsRel, Formula rhsAtt) := rhs[rIdx], \int(_) := rhsAtt || intVar(_) := rhsAtt) {       
      Formula opResult = operation(lhsAtt, rhsAtt);
      
      Atom resultAtom = acf.freshAtom();       
      acf.addAtomToUniverse(atomWithAttributes(resultAtom, [attribute("val", intTheory())]));

      if (\int(_) := opResult) { 
        relResult[[resultAtom]] = relAndAtt(\and(lhs[lIdx].relForm, rhs[rIdx].relForm), opResult);
      } else {
        acf.addAttributeConstraint(equal(toIntVar(resultAtom, "val"), operation(lhsAtt, rhsAtt)));
        
        relResult[[resultAtom]] = relAndAtt(\and(lhs[lIdx].relForm, rhs[rIdx].relForm), toIntVar(resultAtom, "val"));
      }
    } else {
      throw "Can not perform integer arithmetic operation on non selected integer attributes";
    } 
  }

  return relResult;
}  

RelationMatrix translateExpression(sum(Expr e), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix m = translateCachedExpression(e, env, uni, acf, cache);
  
  if (size(getOneFrom(m)) != 1) {
    throw "Relation to sum to should be an unary relation with a single integer attribute";
  }

  Atom resultAtom = acf.freshAtom();
  acf.addAtomToUniverse(atomWithAttributes(resultAtom, [attribute("val", intTheory())]));

  Formula attResult = \int(0);
  for (Index idx <- m) {
    if (relAndAtt(Formula r, Formula a) := m[idx], \int(_) := a || intVar(_) := a) {
      attResult = addition(attResult, ite(r, a, \int(0)));
    } else {
      throw "Can not perform sum on non selected integer attributes";
    } 
  }
  
  acf.addAttributeConstraint(equal(toIntVar(resultAtom, "val"), attResult));
  
  return ([resultAtom] : relAndAtt(\true(), toIntVar(resultAtom, "val")));   
}

RelationMatrix translateExpression(car(Expr e), Environment env, Universe uni, AdditionalConstraintFunctions acf, Cache cache) {
  RelationMatrix m = translateCachedExpression(e, env, uni, acf, cache);

  Atom resultAtom = acf.freshAtom();
  acf.addAtomToUniverse(atomWithAttributes(resultAtom, [attribute("val", intTheory())]));
  
  Formula attResult = \int(0);
  for (Index idx <- m) {
    attResult = addition(attResult, ite(m[idx].relForm, \int(1), \int(0)));
  }
  
  acf.addAttributeConstraint(equal(toIntVar(resultAtom, "val"), attResult));

  return ([resultAtom] : relAndAtt(\true(), toIntVar(resultAtom, "val")));
}
