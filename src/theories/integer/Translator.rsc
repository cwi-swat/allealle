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
 
AttributeFormula constructAttribute(str relName, Atom a, Formula relForm, attribute(str name, intTheory())) = <relForm, equal(intVar("<a>!<name>"),intVar("<a>!<name>"))>;
AttributeFormula constructAttribute(str relName, Atom a, Formula relForm, attributeAndValue(str name, intTheory(), intExpr(Expr expr))) = <relForm, equal(intVar("<a>!<name>"), exprToForm(expr))>; //intVar("<a>!<name>"))>;

Formula exprToForm(intLit(int i))                              = \int(i);
Formula exprToForm(neg(Expr e))                                = neg(exprToForm(e));
Formula exprToForm(attributeLookup(variable(str v), str name)) = var("<v>!<name>"); 
Formula exprToForm(multiplication(list[Expr] terms))           = multiplication([exprToForm(t) | Expr t <- terms]);
Formula exprToForm(division(Expr lhs, Expr rhs))               = division(exprToForm(lhs), exprToForm(rhs));
Formula exprToForm(modulo(Expr lhs, Expr rhs))                 = modulo(exprToForm(lhs), exprToForm(rhs));
Formula exprToForm(addition(list[Expr] terms))                 = addition([exprToForm(t) | Expr t <- terms]);
Formula exprToForm(subtraction(Expr lhs, Expr rhs))            = substraction(exprToForm(lhs), exprToForm(rhs));

Formula translateFormula(gt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return gt(l, r);}, acf)
  when RelationAndAttributes lhs := translateExpression(lhsExpr, env, uni, acf),
       RelationAndAttributes rhs := translateExpression(rhsExpr, env, uni, acf);

Formula translateFormula(gte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return gte(l, r);}, acf)
  when RelationAndAttributes lhs := translateExpression(lhsExpr, env, uni, acf),
       RelationAndAttributes rhs := translateExpression(rhsExpr, env, uni, acf);

Formula translateFormula(lt(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return lt(l, r);}, acf)
  when RelationAndAttributes lhs := translateExpression(lhsExpr, env, uni, acf),
       RelationAndAttributes rhs := translateExpression(rhsExpr, env, uni, acf);

Formula translateFormula(lte(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return lte(l, r);}, acf)
  when RelationAndAttributes lhs := translateExpression(lhsExpr, env, uni, acf),
       RelationAndAttributes rhs := translateExpression(rhsExpr, env, uni, acf);

Formula translateFormula(intEqual(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return equal(l, r);}, acf) 
  when RelationAndAttributes lhs := translateExpression(lhsExpr, env, uni, acf),
       RelationAndAttributes rhs := translateExpression(rhsExpr, env, uni, acf);

Formula translateFormula(intInequal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = translateFormula(lhs, rhs, Formula (Formula l, Formula r) { return inequal(l, r);}, acf) 
  when RelationAndAttributes lhs := translateExpression(lhsExpr, env, uni, acf),
       RelationAndAttributes rhs := translateExpression(rhsExpr, env, uni, acf);

Formula translateFormula(RelationAndAttributes lhs, RelationAndAttributes rhs, Formula (Formula lhsElement, Formula rhsElement) operation, AdditionalConstraintFunctions acf) {
  if (arity(lhs) == 0 || arity(rhs) == 0) { return \true(); }
  
  if (arity(lhs) != 1 || arity(rhs) != 1) {
    println(lhs); println(rhs);
    throw "Unable to perform an integer equation on non-unary relations";
  }
  
  Formula result = \true();
  
  for(Index lhsIdx <- lhs.relation) {
    set[Formula] ors = {};
 
    for (Index rhsIdx <- rhs.relation) {
      if (0 notin lhs.att[lhsIdx] || 0 notin rhs.att[rhsIdx]) {
        throw "Can not perform an integer equation on relations that do not capture integer constraints";
      }
      if (size(lhs.att[lhsIdx][0]) != 1 || size(rhs.att[rhsIdx][0]) != 1) {
        throw "Can only perform an integer equation on selected integer attributes";      
      }
      
      Formula tmpResult = \true(); 
         
      for ({set[AttributeFormula] lhsAttribute} := lhs.att[lhsIdx][0]<1>, {set[AttributeFormula] rhsAttribute} := rhs.att[rhsIdx][0]<1>,
           l:<Formula lhsRelForm, equal(lhsIntVar:intVar(str _), Formula _)> <- lhsAttribute, 
           r:<Formula rhsRelForm, equal(rhsIntVar:intVar(str _), Formula _)> <- rhsAttribute) {
        
        tmpResult = \and(tmpResult, operation(lhsIntVar, rhsIntVar));
        
        acf.addAttributeConstraint(l);
        acf.addAttributeConstraint(r); 
      }
      
      ors += \or(\not(rhs.relation[rhsIdx]), tmpResult); 
    }

    result = \and(result, \or(\not(lhs.relation[lhsIdx]), \and(ors)));
  }    
  
  return result; 
}       

RelationAndAttributes translateExpression(sum(Expr e), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationAndAttributes em = translateExpression(e, env, uni, acf);
  
  if (size(getOneFrom(em.relation)) != 1) {
    throw "Relation to sum to should be an unary relation with a single integer attribute";
  }

  Atom resultAtom = "_r<acf.nextResultNr()>";
  acf.addAtomToUniverse(atomWithAttributes(resultAtom, [attribute("val", intTheory())]));

  Formula attResult = \int(0);
  for (Index idx <- em.relation, str attName <- em.att[idx][0], f:<Formula _, equal(i:intVar(str _), Formula _)> <- em.att[idx][0][attName]) {
    attResult = addition(attResult, ite(em.relation[idx], i, \int(0)));
    acf.addAttributeConstraint(f); 
  }
  
  Index idx = [resultAtom];
  return <(idx:\true()), (idx : (0 : ("val" : {<\true(), equal(intVar("<resultAtom>!val"), attResult)>})))>;   
}

RelationAndAttributes translateExpression(car(Expr e), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationAndAttributes em = translateExpression(e, env, uni, acf);

  Atom resultAtom = "_r<acf.nextResultNr()>";
  acf.addAtomToUniverse(atomWithAttributes(resultAtom, [attribute("val", intTheory())]));

  Formula attResult = \int(0);
  for (Index idx <- em.relation) {
    attResult = addition(attResult, ite(em.relation[idx], \int(1), \int(0)));
  }
  
  Index idx = [resultAtom];
  return <(idx:\true()), (idx : (0 : ("val" : {<\true(), equal(intVar("<resultAtom>!val"), attResult)>})))>;   
}

RelationAndAttributes translateExpression(intLit(int i), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  Atom consAtom = "_c<i>";
  
  acf.addAtomToUniverse(atomWithAttributes(consAtom, [attributeAndValue("cons", intTheory(), intExpr(intLit(i)))]));
  
  Index idx = ["_c<i>"]; 
  return <(idx:\true()),(idx:(0:("cons":{<\true(),equal(intVar("_c<i>!cons"),\int(i))>})))>;
}
  
RelationAndAttributes translateExpression(neg(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationAndAttributes base = translateExpression(expr, env, uni, acf);
  
  AttributeMatrix attResult = ();
  
  for (Index idx <- base.relation, {set[AttributeFormula] attForms} := base.att[idx][0]<1>, af:<Formula _, equal(iv:intVar(str _), Formula _)> <- attForms) {
      Atom resultAtom = "_r<acf.nextResultNr()>";       
      acf.addAtomToUniverse(atomWithAttributes(resultAtom, [attribute("val", intTheory())]));  
        
      attResult[idx] = (0 : ("val" : {<\true(), equal(intVar("<resultAtom>!val"), neg(iv))>}));
      acf.addAttributeConstraint(af);      
  }
  
  return <base.relation, attResult>;
}

RelationAndAttributes translateExpression(addition(list[Expr] terms), Environment env, Universe uni, AdditionalConstraintFunctions acf)
  = translateExpression(terms, Formula (Formula lhs, Formula rhs) { return addition(lhs, rhs); }, \int(0), env, uni, acf);

RelationAndAttributes translateExpression(multiplication(list[Expr] terms), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = translateExpression(terms, Formula (Formula lhs, Formula rhs) { return multiplication(lhs, rhs); }, \int(1), env, uni, acf);


private RelationAndAttributes translateExpression(list[Expr] terms, Formula (Formula lhs, Formula rhs) operation, Formula startAttForm, Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationAndAttributes buildResult([], Formula relForm, Formula attForm) {
    Atom resultAtom = "_r<acf.nextResultNr()>";
    acf.addAtomToUniverse(atomWithAttributes(resultAtom, [attribute("val", intTheory())]));

    Index idx = [resultAtom];
    return <(idx : relForm), (idx : (0 : ("val" : {<\true(), equal(intVar("<resultAtom>!val"), attForm)>})))>;
  }
  
  RelationAndAttributes buildResult([Expr hd, *Expr tl], Formula relForm, Formula attForm) {
    RelationAndAttributes e = translateExpression(hd, env, uni, acf);
    
    RelationMatrix relResult = ();
    AttributeMatrix attResult = (); 
    
    for (Index idx <- e.relation, {set[AttributeFormula] attForms} := e.att[idx][0]<1>, af:<Formula _, equal(iv:intVar(str _), Formula _)> <- attForms) {
      acf.addAttributeConstraint(af);
      RelationAndAttributes tmp = buildResult(tl, \and(relForm, e.relation[idx]), operation(attForm, iv));
      
      relResult += tmp.relation;
      attResult += tmp.att;
    }
    
    return <relResult, attResult>;
  }
  
  return buildResult(terms, \true(), startAttForm);
}

RelationAndAttributes translateExpression(subtraction(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = translateExpression(lhsExpr, rhsExpr, Formula (Formula l, Formula r) {return addition(l,neg(r));}, env, uni, acf);

RelationAndAttributes translateExpression(division(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = translateExpression(lhsExpr, rhsExpr, Formula (Formula l, Formula r) {return division(l,r);}, env, uni, acf);

RelationAndAttributes translateExpression(modulo(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = translateExpression(lhsExpr, rhsExpr, Formula (Formula l, Formula r) {return modulo(l,r);}, env, uni, acf);

private RelationAndAttributes translateExpression(Expr lhsExpr, Expr rhsExpr, Formula (Formula l, Formula r) operation, Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationAndAttributes lhs = translateExpression(lhsExpr, env, uni, acf);
  RelationAndAttributes rhs = translateExpression(rhsExpr, env, uni, acf);
  
  if (size(getOneFrom(lhs.relation)) != 1 || size(getOneFrom(rhs.relation)) != 1) {
    throw "Can only perform binary integer arithmetic of unary base relations";
  } 
  
  RelationMatrix relResult = ();
  AttributeMatrix attResult = ();
  
  for (Index lIdx <- lhs.relation, lhs.relation[lIdx] != \false(), Index rIdx <- rhs.relation, rhs.relation[rIdx] != \false()) {
    Atom resultAtom = "_r<acf.nextResultNr()>";       
    acf.addAtomToUniverse(atomWithAttributes(resultAtom, [attribute("val", intTheory())]));

    Index pIdx = [resultAtom];
    relResult[pIdx] = \and(lhs.relation[lIdx], rhs.relation[rIdx]);
    
    for ({set[AttributeFormula] lhsAttribute} := lhs.att[lIdx][0]<1>, {set[AttributeFormula] rhsAttribute} := rhs.att[rIdx][0]<1>,
       l:<Formula lhsRelForm, equal(lhsIntVar:intVar(str _), Formula _)> <- lhsAttribute, 
       r:<Formula rhsRelForm, equal(rhsIntVar:intVar(str _), Formula _)> <- rhsAttribute) {
              
      if (size(lhsAttribute) != 1 || size(rhsAttribute) != 1) {
        throw "Can only perform arithmetic operation on a single, selected attribute";
      }          
        
      attResult[pIdx] = (0 : ("val" : {<\true(), equal(intVar("<resultAtom>!val"), operation(lhsIntVar, rhsIntVar))>}));
      
      acf.addAttributeConstraint(l);
      acf.addAttributeConstraint(r);
    } 
  }

  return <relResult, attResult>;
}  

//Expr transform(sum(attributeLookup(Expr e, str name)), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
//  Expr expr = transform(e, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);
//   
//  if (list[AtomDecl] ad := getOneFrom(expr@maxTuples), size(ad) != 1) {
//    throw "Summation of none unary relations are not allowed";
//  }
//  
//  int max = size(expr@maxTuples);
//
//  AtomDecl sumResultAtom = atomWithAttributes(newResultAtom(), [attribute("val", intTheory())]);
//  str sumRelName = "_sum_<newRelNr()>";
//
//  addRelation(sumRelName, {sumResultAtom}, {[sumResultAtom]});
//  
//  return attributeLookup(sumBind(variable(sumRelName), e), "val")[@maxTuples={[sumResultAtom]}];
//}
//
////@memo
//Expr transform(car(Expr e), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr) {
//  Expr expr = transform(e, env, uni, newResultAtom, addRelation, addConstraint, newRelNr);
//   
//  int max = size(expr@maxTuples);
// 
//  AtomDecl carResultAtom = atomWithAttributes(newResultAtom(), [attribute("val", intTheory())]);
//  str carRelName = "_car_<newRelNr()>";
//
//  addRelation(carRelName, {carResultAtom}, {[carResultAtom]});
//
//  return attributeLookup(carBind(variable(carRelName), e), "val")[@maxTuples={[carResultAtom]}];
//}