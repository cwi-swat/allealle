module theories::Translator

import logic::Propositional;
import theories::AST;
import theories::Binder; 

import IO;
import List;

alias AdditionalConstraintFunctions = tuple[void (AttributeFormula) addAttributeConstraint, void (Command) addAdditionalCommand, void (AtomDecl) addAtomToUniverse, int () nextResultNr]; 

Environment createInitialEnvironment(Problem p) {
  map[Atom, AtomDecl] atomsWithAttributes = (a : ad | ad:atomWithAttributes(Atom a, list[Attribute] _) <- p.uni.atoms);

  Environment env = (rb.relName:createRelationalMapping(rb, atomsWithAttributes) | RelationalBound rb <- p.bounds);
  
  return env;
}
                                                                                                                                                    
RelationAndAttributes createRelationalMapping(relationalBound(str relName, int arity, list[Tuple] lb, list[Tuple] ub), map[Atom, AtomDecl] atomsWithAttributes) {
  str idxToStr(list[Atom] idx) = intercalate("_", idx);
  
  RelationMatrix relResult = ();
  AttributeMatrix attResult = ();
  
  for (\tuple(list[Atom] idx) <- lb) {
    relResult += (idx : \true());
    attResult += (idx : constructAttributesMap(relName, \true(), idx, atomsWithAttributes));  
  }

  for (\tuple(list[Atom] idx) <- ub, idx notin relResult) {
    relResult += (idx : var("<relName>_<idxToStr(idx)>"));
    attResult += (idx : constructAttributesMap(relName, var("<relName>_<idxToStr(idx)>"), idx, atomsWithAttributes));
  }

  return <relResult,attResult>;
} 
                                           
map[int, Attributes] constructAttributesMap(str relName, Formula relForm, Index idx, map[Atom, AtomDecl] atomsWithAttributes) {
  map[int, Attributes] result = ();
  
  for (int i <- [0..size(idx)], Atom a := idx[i], a in atomsWithAttributes) {
    Attributes attributes = ();
    
    for (Attribute at <- atomsWithAttributes[a].attributes) {
      attributes[at.name] = {constructAttribute(relName, a, relForm, at)};
    }
    
    result[i] = attributes;
  }
  
  return result;
}

default AttributeFormula constructAttribute(str relName, Atom a, Formula relForm, Attribute attr) { throw "No attribute builder found for theory \'<attr.theory>\' for atom \'<a>\'"; } 

alias TranslationResult = tuple[Formula relationalFormula, Formula attributeFormula, set[AtomDecl] newAtoms, list[Command] additionalCommands];
                                                                                            
TranslationResult translateProblem(Problem p, Environment env) {
  set[AttributeFormula] attributeConstraints = {};
  
  void addAttributeConstraint(AttributeFormula constraints) {
    attributeConstraints += constraints;
  }
  
  list[Command] additionalCommands = [];
  void addAdditionalCommand(Command command) {
    additionalCommands += command;  
  }
  
  set[AtomDecl] newAtoms = {};
  void addAtomToUniverse(AtomDecl ad) {
    newAtoms += ad;
  }
  
  int resultNr = 0;
  int getNextResultNr() {
     resultNr += 1;
     return resultNr;
  }

  Formula relForm = (\true() | and(it, r) | AlleFormula f <- p.constraints, Formula r := translateFormula(f, env, p.uni, <addAttributeConstraint, addAdditionalCommand, addAtomToUniverse, getNextResultNr>));
  Formula attForm = (\true() | and(it, r) | AttributeFormula f <- attributeConstraints, Formula r := \if(f.relForm, f.attForm));
  
  return <relForm, attForm, newAtoms, additionalCommands>; 
}

Environment constructSingleton(str newVarName, list[Atom] vector, RelationAndAttributes orig) = (newVarName : <(vector : \true()), (vector: orig.att[vector])>);

Formula translateFormula(empty(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = \not(translateFormula(nonEmpty(expr), env, uni, acf));

Formula translateFormula(atMostOne(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = \or(translateFormula(empty(expr), env, uni, acf), translateFormula(exactlyOne(expr), env, uni, acf));

Formula translateFormula(exactlyOne(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = (\false() | \or(it, \and(m[x], (\true() | \and(it, \not(m[y])) | Index y <- m, y != x))) | Index x <- m)    
    when RelationMatrix m := translateExpression(expr, env, uni, acf).relation;

Formula translateFormula(nonEmpty(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationMatrix m = translateExpression(expr, env, uni, acf).relation;
  
  Formula result = \false();
  
  for (Index idx <- m) {
    if (m[idx] == \true()) {
      return \true();
    }
    
    result = \or(result, m[idx]);
  }
  
  return result;
}

Formula translateFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationMatrix lhs = translateExpression(lhsExpr, env, uni, acf).relation;
  RelationMatrix rhs = translateExpression(rhsExpr, env, uni, acf).relation;
  
  RelationMatrix m = ();
  for (Index idx <- (lhs + rhs)) {
    Formula lhsVal = (idx in lhs) ? lhs[idx] : \false();
    Formula rhsVal = (idx in rhs) ? rhs[idx] : \false();
 
    m[idx] = \or(\not(lhsVal), rhsVal);
    if (m[idx] == \false()) {
      return \false();
    }
  } 

  if (m == ()) {
    return \false();
  }

  Formula result = \true();
  for (Index idx <- m) {  
    result = \and(result, m[idx]);
  }
  
  return result;
}
     
Formula translateFormula(equal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf)
  = \and(translateFormula(subset(lhsExpr, rhsExpr), env, uni, acf), translateFormula(subset(rhsExpr, lhsExpr), env, uni, acf));

Formula translateFormula(inequal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = translateFormula(negation(equal(lhsExpr, rhsExpr)), env, uni, acf);
  
Formula translateFormula(negation(AlleFormula form), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = \not(translateFormula(form, env, uni, acf));

Formula translateFormula(conjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  Formula l = translateFormula(lhsForm, env, uni, acf);
  if (l == \false()) {
    return \false();
  }
  
  return \and(l, translateFormula(rhsForm, env, uni, acf));
}

Formula translateFormula(disjunction(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  Formula l = translateFormula(lhsForm, env, uni, acf);
  if (l == \true()) {
     return \true();
  }
  
  return \or(l, translateFormula(rhsForm, env, uni, acf));
}

Formula translateFormula(implication(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  Formula l = translateFormula(lhsForm, env, uni, acf);
  if (l == \false()) {
    return \true();
  }
  
  return \or(\not(l), translateFormula(rhsForm, env, uni, acf));
}

Formula translateFormula(equality(AlleFormula lhsForm, AlleFormula rhsForm), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  Formula l = translateFormula(lhsForm, env, uni, acf);
  Formula r = translateFormula(rhsForm, env, uni, acf);
  
  return \or(\and(l,r), \and(\not(l), \not(r)));
}

data Formula 
  = substitutes(Environment subs)
  ; 

Formula translateFormula(universal(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  Formula buildOr([], Environment extendedEnvironment) = substitutes(extendedEnvironment);

  Formula buildOr([VarDeclaration hd, *VarDeclaration tl], Environment extendedEnvironment) {
    set[Formula] result = {};
    
    RelationAndAttributes raa = translateExpression(hd.binding, env+ extendedEnvironment, uni, acf);
    RelationMatrix m = raa.relation;

    for (Index idx <- m) {
      Formula clause = buildOr(tl, extendedEnvironment + constructSingleton(hd.name, idx, raa));
    
      if (clause == \false() && m[idx] == \true()) {
        return \false();
      }
      
      result += \or(\not(m[idx]), clause);   
    }    
    
    return \and(result);
  }
  
  Formula result = buildOr(decls, ());
  
  result = visit(result) {
    case substitutes(Environment subs) => translateFormula(form, env + subs, uni, acf)
  }
  
  return result;
}

Formula translateFormula(existential(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  set[Formula] clauses = {};
    
  VarDeclaration hd = decls[0];
  list[VarDeclaration] tl = (size(decls) > 1) ? decls[1..] : [];
  
  RelationAndAttributes raa = translateExpression(hd.binding, env, uni, acf);
  RelationMatrix m = raa.relation;
  
  for (Index x <- m, m[x] != \false()) {
    AlleFormula f = tl != [] ? existential(tl, form) : form;

    Formula clause = \and(m[x], translateFormula(f, env + constructSingleton(hd.name, x, raa), uni, acf));
    
    if (clause == \true()) { return \true(); }
    clauses += clause;
  }
  
  return \or(clauses);
}

default Formula translateFormula(AlleFormula f, Environment env, Universe uni, AdditionalConstraintFunctions acf) { throw "Translation of formula \'<f>\' not supported"; }

RelationAndAttributes translateExpression(variable(str name), Environment env, Universe uni, AdditionalConstraintFunctions acf) = env[name];
RelationAndAttributes translateExpression(attributeLookup(Expr e, str name), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationAndAttributes m = translateExpression(e, env, uni, acf);
  
  if (arity(m) != 1) {
    throw "Can only lookup attributes on an unary relation";
  }
  
  AttributeMatrix attResult = ();
  for (Index idx <- m.att) {
    if (name notin m.att[idx][0]) {
      throw "Attribute \'<name>\' not present on relation";
    }
    
    attResult[idx] = (0: (name : m.att[idx][0][name]));
  }
  
  return <m.relation, attResult>;   
}

RelationAndAttributes translateExpression(transpose(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = transpose(m)
  when RelationAndAttributes m := translateExpression(expr, env, uni, acf); 

RelationAndAttributes translateExpression(closure(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = transitiveClosure(m)
  when RelationAndAttributes m := translateExpression(expr, env, uni, acf);

RelationAndAttributes translateExpression(reflexClosure(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = reflexiveTransitiveClosure(m, uni)
  when RelationAndAttributes m := translateExpression(expr, env, uni, acf);

RelationAndAttributes translateExpression(union(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = or(lhs,rhs)  
  when RelationAndAttributes lhs := translateExpression(lhsExpr, env, uni, acf),
       RelationAndAttributes rhs := translateExpression(rhsExpr, env, uni, acf);

RelationAndAttributes translateExpression(intersection(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = and(lhs, rhs)
  when RelationAndAttributes lhs := translateExpression(lhsExpr, env, uni, acf),
       RelationAndAttributes rhs := translateExpression(rhsExpr, env, uni, acf);

RelationAndAttributes translateExpression(difference(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = difference(lhs, rhs)
  when RelationAndAttributes lhs := translateExpression(lhsExpr, env, uni, acf),
       RelationAndAttributes rhs := translateExpression(rhsExpr, env, uni, acf);

RelationAndAttributes translateExpression(\join(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = \join(lhs, rhs) 
  when RelationAndAttributes lhs := translateExpression(lhsExpr, env, uni, acf), 
       RelationAndAttributes rhs := translateExpression(rhsExpr, env, uni, acf);

RelationAndAttributes translateExpression(accessorJoin(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = translateExpression(\join(rhsExpr, lhsExpr), env, uni, acf);

RelationAndAttributes translateExpression(product(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = product(lhs, rhs)
  when RelationAndAttributes lhs := translateExpression(lhsExpr, env, uni, acf), 
       RelationAndAttributes rhs := translateExpression(rhsExpr, env, uni, acf);

RelationAndAttributes translateExpression(ifThenElse(AlleFormula caseForm, Expr thenExpr, Expr elseExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  Formula \case = translateFormula(caseForm, env, uni, acf);
  RelationAndAttributes then = translateExpression(thenExpr, env, uni, acf);
  RelationAndAttributes \else = translateExpression(elseExpr, env, uni, acf);

  if (arity(then) != arity(\else)) {
    throw "Then and Else expressions must be of same arity";
  }

  if (\case == \true()) {
    return then;
  } else if (\case == \false()) {
    return \else;
  } 
  
  RelationMatrix relResult = ();
  AttributeMatrix attResult = ();
  
  for (Index idx <- (then.relation + \else.relation)) {
    Formula thenRel = ((idx in then.relation) ? then.relation[idx] : \false());
    Formula elseRel = ((idx in \else.relation) ? \else.relation[idx] : \false()); 
    map[int, Attributes] thenAtt = ((idx in then.att) ? then.att[idx] : ());
    map[int, Attributes] elseAtt = ((idx in \else.att) ? \else.att[idx] : ());
    
    relResult[idx] = ite(\case, thenRel, elseRel);
    attResult[idx] = merge(thenAtt,elseAtt); 
  } 
  
  return <relResult,attResult>;
}

RelationAndAttributes translateExpression(comprehension(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationAndAttributes calculate(Index idx, [], Environment extendedEnv, Formula partialRelForm, map[int, Attributes] attributes) {
    if (partialRelForm == \false()) {
      return <(idx:\false()), (idx:attributes)>;
    }
    
    return <(idx : and(partialRelForm, translateFormula(form, extendedEnv, uni,acf))), (idx:attributes)>;
  }
  
  RelationAndAttributes calculate(Index currentIdx, [VarDeclaration hd, *VarDeclaration tl], Environment extendedEnv, Formula partialRelForm, map[int, Attributes] attributes) {
    RelationMatrix relResult = ();
    AttributeMatrix attResult = ();
    
    RelationAndAttributes decl = translateExpression(hd.binding, extendedEnv, uni, acf);
    if (arity(decl) > 1) { throw "Higher order comprehensions are not allowed"; }
    
    for (Index idx <- decl.relation) {
      RelationAndAttributes tmp = calculate(currentIdx + idx, tl, extendedEnv + constructSingleton(hd.name, idx, decl), \and(partialRelForm, decl.relation[idx]), attributes + (i + size(idx) : decl.att[idx][i] | int i <- decl.att[idx]));
      relResult += tmp.relation;
      attResult += tmp.att;
    } 
    
    return <relResult, attResult>;
  }
  
  return calculate([], decls, env, \true(), ());
}

default RelationAndAttributes translateExpression(Expr expr, Environment env, Universe uni, AdditionalConstraintFunctions acf) { throw "Translation of expression \'<expr>\' not supported"; }
