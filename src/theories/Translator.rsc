module theories::Translator

import logic::Propositional;
import theories::AST;
import theories::Binder; 

import IO;
import List;

alias AdditionalConstraintFunctions = tuple[void (Formula) addAttributeConstraint, void (Command) addAdditionalCommand, void (AtomDecl) addAtomToUniverse, Atom () freshAtom]; 

Environment createInitialEnvironment(Problem p) {
  map[str, RelationMatrix] relations = (rb.relName:createRelationalMapping(rb) | RelationalBound rb <- p.bounds);
  map[Atom, map[str, Formula]] attributes = (a : createAttributeMap(ad) | ad:atomWithAttributes(Atom a, list[Attribute] attributes) <- p.uni.atoms); 
  
  return <relations, attributes>;
} 
                                                                                                                                                    
RelationMatrix createRelationalMapping(relationalBound(str relName, int arity, list[Tuple] lb, list[Tuple] ub)) {
  str idxToStr(list[Atom] idx) = intercalate("_", idx);
  
  RelationMatrix relResult = ();
  
  for (\tuple(list[Atom] idx) <- lb) {
    relResult += (idx : relOnly(\true()));
  }

  for (\tuple(list[Atom] idx) <- ub, idx notin relResult) {
    relResult += (idx : relOnly(var("<relName>_<idxToStr(idx)>")));
  }

  return relResult;
} 
                                           
map[str, Formula] createAttributeMap(AtomDecl ad) = (at.name : constructAttribute(ad.atom, at) | Attribute at <- ad.attributes);  

default Formula constructAttribute(Atom a, Attribute attr) { throw "No attribute builder found for theory \'<attr.theory>\' for atom \'<a>\'"; } 

alias TranslationResult = tuple[Formula relationalFormula, Formula attributeFormula, set[AtomDecl] newAtoms, list[Command] additionalCommands];
                                                                                            
TranslationResult translateProblem(Problem p, Environment env) {
  set[Formula] attributeConstraints = {};
  
  void addAttributeConstraint(Formula constraint) {
    attributeConstraints += constraint;
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
  Atom freshAtom() {
     resultNr += 1;
     return "_tmp<resultNr>";
  }

  Formula relForm = (\true() | and(it, r) | AlleFormula f <- p.constraints, Formula r := translateFormula(f, env, p.uni, <addAttributeConstraint, addAdditionalCommand, addAtomToUniverse, freshAtom>));
  Formula attForm = (\true() | and(it, f) | Formula f <- attributeConstraints);
  
  return <relForm, attForm, newAtoms, additionalCommands>; 
}

map[str, RelationMatrix] constructSingleton(str newVarName, list[Atom] vector) = (newVarName : (vector : relOnly(\true())));

Formula translateFormula(empty(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = \not(translateFormula(nonEmpty(expr), env, uni, acf));

Formula translateFormula(atMostOne(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = \or(translateFormula(empty(expr), env, uni, acf), translateFormula(exactlyOne(expr), env, uni, acf));

Formula translateFormula(exactlyOne(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = (\false() | \or(it, \and(m[x].relForm, (\true() | \and(it, \not(m[y].relForm)) | Index y <- m, y != x))) | Index x <- m)    
    when RelationMatrix m := translateExpression(expr, env, uni, acf);

Formula translateFormula(nonEmpty(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationMatrix m = translateExpression(expr, env, uni, acf);
  
  Formula result = \false();
  
  for (Index idx <- m) {
    if (m[idx].relForm == \true()) {
      return \true();
    }
    
    result = \or(result, m[idx].relForm);
  } 
  
  return result;
}

Formula translateFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationMatrix lhs = translateExpression(lhsExpr, env, uni, acf);
  RelationMatrix rhs = translateExpression(rhsExpr, env, uni, acf);
  
  RelationMatrix m = ();
  for (Index idx <- (lhs + rhs)) {
    Formula lhsVal = (idx in lhs) ? lhs[idx].relForm : \false();
    Formula rhsVal = (idx in rhs) ? rhs[idx].relForm : \false();
 
    m[idx] = relOnly(\or(\not(lhsVal), rhsVal));
    if (m[idx].relForm == \false()) {
      return \false();
    }
  } 

  if (m == ()) {
    return \false();
  }

  Formula result = \true();
  for (Index idx <- m) {  
    result = \and(result, m[idx].relForm);
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

private Environment extEnv(Environment orig, map[str, RelationMatrix] newRelations) = <orig.relations + newRelations, orig.attributes>; 

data Formula 
  = substitutes(Environment subs)
  ; 

Formula translateFormula(universal(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  
  Formula buildOr([], map[str,RelationMatrix] extraBindings) = substitutes(extEnv(env, extraBindings));

  Formula buildOr([VarDeclaration hd, *VarDeclaration tl], map[str,RelationMatrix] extraBindings) {
    set[Formula] result = {};
    
    RelationMatrix m = translateExpression(hd.binding, extEnv(env, extraBindings), uni, acf);

    for (Index idx <- m) {
      Formula clause = buildOr(tl, extraBindings + constructSingleton(hd.name, idx));
    
      if (clause == \false() && m[idx].relForm == \true()) {
        return \false();
      }
      
      result += \or(\not(m[idx].relForm), clause);   
    }    
    
    return \and(result);
  }
  
  Formula result = buildOr(decls, ());
  
  result = visit(result) {
    case substitutes(Environment subs) => translateFormula(form, subs, uni, acf)
  }
  
  return result;
}

Formula translateFormula(existential(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  set[Formula] clauses = {};
    
  VarDeclaration hd = decls[0];
  list[VarDeclaration] tl = (size(decls) > 1) ? decls[1..] : [];
  
  RelationMatrix m = translateExpression(hd.binding, env, uni, acf);
  
  for (Index x <- m, m[x].relForm != \false()) {
    AlleFormula f = tl != [] ? existential(tl, form) : form;

    Formula clause = \and(m[x].relForm, translateFormula(f, extEnv(env, constructSingleton(hd.name, x)), uni, acf));
    
    if (clause == \true()) { return \true(); }
    clauses += clause;
  }
  
  return \or(clauses);
}

default Formula translateFormula(AlleFormula f, Environment env, Universe uni, AdditionalConstraintFunctions acf) { throw "Translation of formula \'<f>\' not supported"; }

RelationMatrix translateExpression(variable(str name), Environment env, Universe uni, AdditionalConstraintFunctions acf) = env.relations[name];
RelationMatrix translateExpression(attributeLookup(Expr e, str name), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationMatrix m = translateExpression(e, env, uni, acf);
  
  if (arity(m) != 1) {
    throw "Can only lookup attributes on an unary relation";
  }
  
  for (idx:[Atom a] <- m) {
    if (a notin env.attributes || name notin env.attributes[a]) {
      throw "Attribute \'<name>\' not defined on \'<a>\' ";
    }
    
    m[idx] = relAndAtt(m[idx].relForm, env.attributes[a][name]);
  }
  
  return m;   
}

RelationMatrix translateExpression(transpose(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = transpose(m)
  when RelationMatrix m := translateExpression(expr, env, uni, acf); 

RelationMatrix translateExpression(closure(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = transitiveClosure(m)
  when RelationMatrix m := translateExpression(expr, env, uni, acf);

RelationMatrix translateExpression(reflexClosure(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = reflexiveTransitiveClosure(m, uni)
  when RelationMatrix m := translateExpression(expr, env, uni, acf);

RelationMatrix translateExpression(union(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = or(lhs,rhs)  
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, acf);

RelationMatrix translateExpression(intersection(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = and(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, acf);

RelationMatrix translateExpression(difference(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = difference(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, acf),
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, acf);

RelationMatrix translateExpression(\join(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = \join(lhs, rhs) 
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, acf), 
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, acf);

RelationMatrix translateExpression(accessorJoin(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = translateExpression(\join(rhsExpr, lhsExpr), env, uni, acf);

RelationMatrix translateExpression(product(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = product(lhs, rhs)
  when RelationMatrix lhs := translateExpression(lhsExpr, env, uni, acf), 
       RelationMatrix rhs := translateExpression(rhsExpr, env, uni, acf);

RelationMatrix translateExpression(ifThenElse(AlleFormula caseForm, Expr thenExpr, Expr elseExpr), Environment env, Universe uni, AdditionalConstraintFunctions acf) = ite(\case, then, \else)
  when Formula \case := translateFormula(caseForm, env, uni, acf),
       RelationMatrix then := translateExpression(thenExpr, env, uni, acf),
       RelationMatrix \else := translateExpression(elseExpr, env, uni, acf);

RelationMatrix translateExpression(comprehension(list[VarDeclaration] decls, AlleFormula form), Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationMatrix calculate(Index idx, [], Environment extendedEnv, Formula partialRelForm) {
    if (partialRelForm == \false()) {
      return (idx:relOnly(\false()));
    }
    
    return (idx : relOnly(and(partialRelForm, translateFormula(form, extendedEnv, uni,acf))));
  }
  
  RelationMatrix calculate(Index currentIdx, [VarDeclaration hd, *VarDeclaration tl], Environment extendedEnv, Formula partialRelForm) {
    RelationMatrix relResult = ();
    
    RelationMatrix decl = translateExpression(hd.binding, extendedEnv, uni, acf);
    if (arity(decl) > 1) { throw "Higher order comprehensions are not allowed"; }
    
    for (Index idx <- decl) {
      relResult += calculate(currentIdx + idx, tl, extEnv(extendedEnv, constructSingleton(hd.name, idx)), \and(partialRelForm, decl[idx].relForm));
    } 
    
    return relResult;
  }
  
  return calculate([], decls, env, \true());
}

default RelationMatrix translateExpression(Expr expr, Environment env, Universe uni, AdditionalConstraintFunctions acf) { throw "Translation of expression \'<expr>\' not supported"; }
