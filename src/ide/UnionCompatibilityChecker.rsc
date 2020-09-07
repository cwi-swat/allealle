module ide::UnionCompatibilityChecker

import translation::Syntax;

import ParseTree;
import Message;
import Map;
import String;
import Set;
import List;
import util::Maybe;

data UnionResult 
  = heading(map[str,str] attributes)
  | incompatible()
  ;
  
alias UnionCompatibilityResult = tuple[map[loc, UnionResult] headings, set[Message] messages];

alias CheckFunctions = tuple[void (loc,UnionResult) add, UnionResult (loc) lookup, Maybe[list[UnionResult]] (str) lookupPred, void (Message) addMessage];
alias Environment = map[str,UnionResult];
  
str heading2Str(heading(map[str,str] attributes)) = intercalate(",", ["<h>:<attributes[h]>" | h <- attributes]);  
  
UnionCompatibilityResult checkUnionCompatibilty(Problem p) {  
  set[Message] messages = {};

  map[loc,UnionResult] headings = ();
  void add(loc l,UnionResult r) {
    headings[l] = r;
  }
  UnionResult lookup(loc l) = (l in headings) ? headings[l] : incompatible();
  
  map[str name, list[UnionResult] params] predicates = ("<pred.name>" : [heading(("<ha.name>":"<ha.dom>()" | ha <- param.header)) | param <- pred.params] | (AlleConstraint)`<AllePredicate pred>` <- p.constraints);
  Maybe[list[UnionResult]] lookupPred(str predName) = predName in predicates ? just(predicates[predName]) : nothing();
  
  void addMsg(Message m) { messages += m; }
  
  Environment env = buildEnvironment(p);  
  
  for ((AlleConstraint)`<AllePredicate pr>` <- p.constraints) {
    check(pr, env, <add,lookup,lookupPred,addMsg>);
  }
  
  for ((AlleConstraint)`<AlleFormula f>` <- p.constraints) {
    check(f,env,<add,lookup,lookupPred,addMsg>);
  }
  
  for (/AlleExpr e := p.objSection) {
    check(e,env,<add,lookup,lookupPred,addMsg>);
  }
  
  return <headings,messages>; 
} 

void addIfCompatible(loc base, AlleExpr lhs, AlleExpr rhs, Environment env, CheckFunctions cf) {
  check(lhs, env, cf);
  check(rhs, env, cf);

  if (heading(map[str,str] lhsAtts) := cf.lookup(lhs@\loc), heading(map[str,str] rhsAtts) := cf.lookup(rhs@\loc)) {
    if (lhsAtts == rhsAtts) {
      cf.add(base, cf.lookup(lhs@\loc));
    } else {
      cf.add(base, incompatible());
      cf.addMessage(error("\'<lhsAtts>\' is not union compatible with \'<rhsAtts>\'", base));
    }
  } else {
    cf.add(base, incompatible());
  }
}


map[str,UnionResult] buildEnvironment(Problem p) {
  Environment env = ();

  visit(p.relations) {
    case (Relation)`<RelVar v> (<{HeaderAttribute ","}+ header>) <RelationalBound _>`: env["<v>"] = heading(("<ha.name>":"<ha.dom>()" | HeaderAttribute ha <- header));
  }
  
  return env;
}

//void check((RelationalBound)`= {<{Tuple ","}* tuples> }`, map[str,str] attributes, CheckFunctions cf) {
//  check({t | t <- tuples}, attributes, cf);
//}
//void check((RelationalBound)`\<= {<{Tuple ","}* upper> }`, map[str,str] attributes, CheckFunctions cf) {
//  check({t | t <- upper}, attributes, cf);
//}
//
//void check((RelationalBound)`\>= {<{Tuple ","}* lower>} \<= {<{Tuple ","}* upper> }`, map[str,str] attributes, CheckFunctions cf) { checkTuples({t | t <- lower}, attributes, cf); checkTuples({t | t <- upper}, attributes, cf);}
//
//void checkTuples(set[Tuple] tuples, map[str,str] attributes, CheckFunctions cf) {
//  for (t <- tuples) {
//    check(t, attributes, cf);
//  }
//}

void check((AllePredicate)`pred <Idd _>[<{PredParam ","}* params>] = <AlleFormula form>`, Environment env, CheckFunctions cf) {
  for (p <- params) {
    env += ("<p.name>" : heading(("<ha.name>":"<ha.dom>()" | ha <- p.header))); 
  }
  
  check(form, env, cf);
}

void check(cur:(AlleFormula)`<Idd predName>[<{AlleExpr ","}* arguments>]`, Environment env, CheckFunctions cf) {
  Maybe[list[UnionResult]] formals = cf.lookupPred("<predName>");
  
  if (nothing() := formals) {
    cf.addMessage(error("Predicate with name `<predName>` is not declared", cur@\loc));
    return;
  } 

  list[AlleExpr] args = [];
  for (a <- arguments) {
    check(a, env, cf);
    args += a;
  }

  if (size(args) != size(formals.val)) {
    cf.addMessage(error("Incompatible number of arguments", cur@\loc));  
  } else {
    if ([incompatible()] != formals.val) {
      for (int i <- [0..size(formals.val)]) {
        argHeading = cf.lookup(args[i]@\loc);
        if (argHeading != incompatible(), formals.val[i] != argHeading) {
          cf.addMessage(error("Argument `<args[i]>` is not union compatible with `<heading2Str(formals.val[i])>`", args[i]@\loc)); 
        }
      }  
    }
  }   
}
 
void check((AlleFormula)`( <AlleFormula form> )`, Environment env, CheckFunctions cf) { check(form, env, cf); } 
void check((AlleFormula)`¬ <AlleFormula form>`, Environment env, CheckFunctions cf) { check(form, env, cf); }
void check((AlleFormula)`no <AlleExpr expr>`, Environment env, CheckFunctions cf)  { check(expr, env, cf); }
void check((AlleFormula)`lone <AlleExpr expr>`, Environment env, CheckFunctions cf)  { check(expr, env, cf); }
void check((AlleFormula)`one <AlleExpr expr>`, Environment env, CheckFunctions cf)  { check(expr, env, cf); }
void check((AlleFormula)`some <AlleExpr expr>`, Environment env, CheckFunctions cf)  { check(expr, env, cf); }

void check(f:(AlleFormula)`<AlleExpr lhs> ⊆ <AlleExpr rhs>`, Environment env, CheckFunctions cf) { addIfCompatible(f@\loc, lhs, rhs, env, cf); }
void check(f:(AlleFormula)`<AlleExpr lhs> = <AlleExpr rhs>`, Environment env, CheckFunctions cf) { addIfCompatible(f@\loc, lhs, rhs, env, cf); }
void check(f:(AlleFormula)`<AlleExpr lhs> ≠ <AlleExpr rhs>`, Environment env, CheckFunctions cf) { addIfCompatible(f@\loc, lhs, rhs, env, cf); }
void check(f:(AlleFormula)`<AlleExpr lhs> != <AlleExpr rhs>`, Environment env, CheckFunctions cf) { addIfCompatible(f@\loc, lhs, rhs, env, cf); }

void check(f:(AlleFormula)`<AlleFormula lhs> ∧ <AlleFormula rhs>`, Environment env, CheckFunctions cf)  { check(lhs, env, cf); check(rhs, env, cf); }
void check(f:(AlleFormula)`<AlleFormula lhs> ∨ <AlleFormula rhs>`, Environment env, CheckFunctions cf)  { check(lhs, env, cf); check(rhs, env, cf); }
void check(f:(AlleFormula)`<AlleFormula lhs> ⇒ <AlleFormula rhs>`, Environment env, CheckFunctions cf)  { check(lhs, env, cf); check(rhs, env, cf); }
void check(f:(AlleFormula)`<AlleFormula lhs> ⇔ <AlleFormula rhs>`, Environment env, CheckFunctions cf)  { check(lhs, env, cf); check(rhs, env, cf); }

void check(f:(AlleFormula)`let <{VarBinding ","}+ bindings> | <AlleFormula form>`, Environment env, CheckFunctions cf)  {
  for (VarBinding vb <- bindings) {
    env += checkBinding(vb, env, cf);
  }
  
  check(form, env, cf);
}

Environment checkBinding(VarBinding binding, Environment env, CheckFunctions cf) {
  check(binding.expr, env,cf);
  
  env["<binding.var>"] = cf.lookup(binding.expr@\loc);
  return env;
}

void check(f:(AlleFormula)`∀ <{VarDeclaration ","}+ decls> | <AlleFormula form>`, Environment env, CheckFunctions cf)  {
  for (VarDeclaration vd <- decls) {
    env += checkDeclaration(vd, env, cf);
  }
  check(form, env, cf);
} 

void check(f:(AlleFormula)`∃ <{VarDeclaration ","}+ decls> | <AlleFormula form>`, Environment env, CheckFunctions cf)  {
  for (VarDeclaration vd <- decls) {
    env += checkDeclaration(vd, env, cf);
  }
  check(form, env, cf);
}

Environment checkDeclaration(VarDeclaration decl, Environment env, CheckFunctions cf) {
  check(decl.expr, env,cf);
  
  env["<decl.var>"] = cf.lookup(decl.expr@\loc);
  return env;
}
 
void check(e:(AlleExpr)`(<AlleExpr expr>)`, Environment env, CheckFunctions cf)  { 
  check(expr, env, cf); 
  cf.add(e@\loc, cf.lookup(expr@\loc));
}

void check((AlleExpr)`<RelVar v>`, Environment env, CheckFunctions cf)  { 
  if ("<v>" in env) {
    cf.add(v@\loc, env["<v>"]); 
  } else {
    cf.add(v@\loc, incompatible());
    cf.addMessage(error("Unknown relational variable", v@\loc));
  }
}

void check((AlleExpr)`<Literal l>`, Environment env, CheckFunctions cf) {}

void check(e:(AlleExpr)`<AlleExpr expr>[<{Rename ","}+ ren>]`, Environment env, CheckFunctions cf) {
  check(expr, env, cf);
  
  map[str,str] renamings = ("<r.orig>":"<r.new>" | r <- ren);
  checkRename(e@\loc, expr@\loc, renamings, cf);
}

private void checkRename(loc e, loc alleExpr, map[str,str] renamings, CheckFunctions cf) {
  if (heading(map[str,str] attributes) := cf.lookup(alleExpr)) {
    set[str] nonExistingAtts = renamings<0> - attributes<0>;
    if (nonExistingAtts != {}) {
      cf.add(e, incompatible());
      cf.addMessage(error("Attributes \'<nonExistingAtts>\' in the renaming do not exists in the relation",e));       
    } else {
      map[str,str] renamed = ((old in renamings ? renamings[old] : old) : attributes[old] | str old <- attributes);
      if (size(renamed) != size(attributes)) {
        cf.add(e, incompatible());
        cf.addMessage(error("Renaming collides with existing attributes",e));       
      } else {
        cf.add(e, heading(renamed));
      }
    }  
  } else {
    cf.add(e, incompatible());
  }
} 

void check(e:(AlleExpr)`<AlleExpr expr>[<{AttributeName ","}+ atts>]`, Environment env, CheckFunctions cf) {
  check(expr, env, cf);
  
  set[str] projectedAtts = {"<att>" | AttributeName att <- atts};
  checkProjection(e@\loc, expr@\loc, projectedAtts, cf);
}

private void checkProjection(loc e, loc alleExpr, set[str] projectedAtts, CheckFunctions cf) {
  if (heading(map[str,str] attributes) := cf.lookup(alleExpr)) {
   if (projectedAtts & attributes<0> != projectedAtts) {
    cf.add(e, incompatible());
    cf.addMessage(error("Not all projected attributes are in the relation", e));
   } else {
    cf.add(e, heading((a : attributes[a] | str a <- projectedAtts)));
   }
  } else {
    cf.add(e, incompatible());
  }  
}

void check(e:(AlleExpr)`<AlleExpr expr>[<{ProjectAndRename ","}+ rp>]`, Environment env, CheckFunctions cf) {
  check(expr, env, cf);
  
  map[str,str] renamings = ("<r.orig>":"<r.new>" | r <- rp);
  checkProjection(e@\loc, expr@\loc, renamings<0>, cf); 
  checkRename(e@\loc, e@\loc, renamings, cf);
}


void check(e:(AlleExpr)`<AlleExpr expr>[<{AggregateFunctionDef ","}+ aggFuncs>]`, Environment env, CheckFunctions cf) {
  check(expr, env, cf);
  
  if (heading(map[str,str] attributes) := cf.lookup(expr@\loc)) {  
    map[str,str] newHeading = ();
    for (AggregateFunctionDef def <- aggFuncs) {
      check(def, attributes, cf);
      if (heading(map[str,str] newAtts) := cf.lookup(def@\loc)) {
        newHeading += newAtts;
      } 
    }
    
    if (newHeading != ()) {
      cf.add(e@\loc, heading(newHeading));
    } else {
      cf.add(e@\loc, incompatible());
    }
  } else {
    cf.add(e@\loc, incompatible());
  } 
}

void check(e:(AlleExpr)`<AlleExpr expr>[<{AttributeName ","}+ groupBy>,<{AggregateFunctionDef ","}+ aggFuncs>]`, Environment env, CheckFunctions cf) {
  check(expr, env, cf);
  
  if (heading(map[str,str] attributes) := cf.lookup(expr@\loc)) {  
    bool err = false;
    
    for (AttributeName group <- groupBy) {
      if ("<group>" notin attributes) {
        cf.addMessage(error("Attribute is not part of relation", group@\loc));
        cf.add(e@\loc, incompatible()); 
        err = true;
      } else if (attributes["<group>"] != "id()") {
        cf.addMessage(error("Can only group on id attributes", group@\loc));
        cf.add(e@\loc, incompatible()); 
        err = true;
      }
    }
    
    if (!err) {
      map[str,str] newHeading = ();
      for (AggregateFunctionDef def <- aggFuncs) {
        check(def, attributes, cf);
        if (heading(map[str,str] newAtts) := cf.lookup(def@\loc)) {
          newHeading += newAtts;
        } 
      }
      
      if (newHeading != ()) {
        cf.add(e@\loc, heading(newHeading));
      } else {
        cf.add(e@\loc, incompatible());
      }
    }
  } else {
    cf.add(e@\loc, incompatible());
  } 
}


void check(e:(AlleExpr)`<AlleExpr expr> where <Criteria crit>`, Environment env, CheckFunctions cf) {
  check(expr,env,cf);
  
  if (h:heading(map[str,str] atts) := cf.lookup(expr@\loc)) {
    cf.add(e@\loc,h);
    check(crit, atts, cf);
  }
}
  
void check(e:(AlleExpr)`~<AlleExpr expr>`, Environment env, CheckFunctions cf) { 
  check(expr,env,cf);
  checkBinaryIdRel(e@\loc, cf);
}
    
void check(e:(AlleExpr)`^<AlleExpr expr>`, Environment env, CheckFunctions cf) { 
  check(expr,env,cf);
  checkBinaryIdRel(e@\loc, cf);
}

void check(e:(AlleExpr)`*<AlleExpr expr>`, Environment env, CheckFunctions cf) { 
  check(expr,env,cf);
  checkBinaryIdRel(e@\loc, cf);
}

void checkBinaryIdRel(loc expr, CheckFunctions cf) {
  if (heading(map[str,str] attributes) := cf.lookup(expr)) {
    list[str] atts = toList(domain(attributes));
    
    if (size(atts) != 2 || attributes[atts[0]] != id() || attributes[atts[1]] != id()) {
      cf.add(expr,incompatible());
      cf.addMessage(error("Can only operate on a binary relation with two id attributes", expr));      
    } else {
      cf.add(expr,heading(attributes));
    } 
  } else {
    cf.add(expr, incompatible());
  }
}

void checkTasAgaintsAttributes(loc base, loc expr, TupleAttributeSelection tas, CheckFunctions cf) {
  if (heading(map[str,str] attributes) := cf.lookup(expr)) {
    if (attributes<0> != {"<tas.first>","<tas.second>"}) {
      cf.add(base,incompatible());
      cf.addMessage(error("Attributes \'<tas>\' do not match the attributes in the relation", base));
    } else {
      cf.add(base,heading(attributes));
    }
  } else {
    cf.add(base, incompatible());
  }
}
  
void check(e:(AlleExpr)`<AlleExpr lhs> ⨝ <AlleExpr rhs>`, Environment env, CheckFunctions cf) {
  check(lhs,env,cf);
  check(rhs,env,cf);
  
  if (heading(map[str,str] attLhs) := cf.lookup(lhs@\loc), heading(map[str,str] attRhs) := cf.lookup(rhs@\loc)) {
    if (attLhs & attRhs == ()) {
      cf.add(e@\loc, incompatible());
      cf.addMessage(error("No overlapping attributes to join", e@\loc));
    } else {
      cf.add(e@\loc, heading(attLhs + attRhs));
    }
  } else {
    cf.add(e@\loc, incompatible());
  } 
}
  
void check(e:(AlleExpr)`<AlleExpr lhs> ∪ <AlleExpr rhs>`, Environment env, CheckFunctions cf)  { addIfCompatible(e@\loc, lhs, rhs, env, cf); }
void check(e:(AlleExpr)`<AlleExpr lhs> ∩ <AlleExpr rhs>`, Environment env, CheckFunctions cf)  { addIfCompatible(e@\loc, lhs, rhs, env, cf); }
void check(e:(AlleExpr)`<AlleExpr lhs> ∖ <AlleExpr rhs>`, Environment env, CheckFunctions cf)  { addIfCompatible(e@\loc, lhs, rhs, env, cf); }
  
void check(e:(AlleExpr)`<AlleExpr lhs> ⨯ <AlleExpr rhs>`, Environment env, CheckFunctions cf) { 
  check(lhs,env,cf);
  check(rhs,env,cf);
  
  if (heading(map[str,str] attLhs) := cf.lookup(lhs@\loc), heading(map[str,str] attRhs) := cf.lookup(rhs@\loc)) {
    if (attLhs & attRhs != ()) {
      cf.add(e@\loc, incompatible());
      cf.addMessage(error("Relations must have distinct attributes, attribute(s) \'<intercalate(",", toList((attLhs & attRhs)<0>))>\' overlaps", e@\loc));
    } else {
      cf.add(e@\loc, heading(attLhs + attRhs));
    }
  } else {
    cf.add(e@\loc, incompatible());
  } 
}

void check(e:(AlleExpr)`{ <{VarDeclaration ","}+ decls> | <AlleFormula form> }`, Environment env, CheckFunctions cf) {
  list[UnionResult] headings = [];
  for (VarDeclaration vd <- decls) {
    env += checkDeclaration(vd, env, cf);
    headings += cf.lookup(vd.expr@\loc);
  }
  
  // The headings must be distinct since the comprehension results in a new relation of which the heading is the product of the headings of all the relations in the declarations
  map[str,str] distinctAtts = ();
  map[str,str] overlappingAtts = ();
  for (heading(map[str,str] atts) <- headings) {
  	overlappingAtts += distinctAtts & atts; 
    distinctAtts += atts;
  }
  
  if (overlappingAtts != ()) {
    cf.add(e@\loc, incompatible());
    cf.addMessage(error("Relations must have distinct attributes, attribute(s) \'<intercalate(",", toList(overlappingAtts<0>))>\' overlap", e@\loc));
  } else {
  	cf.add(e@\loc, heading(distinctAtts)); 
  }
   
  check(form, env, cf);
}

void check(e:(AggregateFunctionDef)`<AggregateFunction func>`, map[str,str] attributes, CheckFunctions cf) {
  check(func, attributes, cf);    
  
  cf.add(e@\loc, heading(("<replaceAll(replaceAll("<func>","(","_"),")","")>":"int()")));
}

void check(e:(AggregateFunctionDef)`<AggregateFunction func> as <AttributeName bindTo>`, map[str,str] attributes, CheckFunctions cf) {
  check(func, attributes, cf);    
  
  cf.add(e@\loc, heading(("<bindTo>":"int()")));
}

void check(e:(AggregateFunction)`count()`, map[str,str] attributes, CheckFunctions cf) {}
void check(e:(AggregateFunction)`sum(<AttributeName att>)`, map[str,str] attributes, CheckFunctions cf) {
  if ("<att>" notin attributes) {
    cf.addMessage(error("\'<att>\' not part of relation", att@\loc));
  }
}
void check(e:(AggregateFunction)`min(<AttributeName att>)`, map[str,str] attributes, CheckFunctions cf) {
  if ("<att>" notin attributes) {
    cf.addMessage(error("\'<att>\' not part of relation", att@\loc));
  }
}
void check(e:(AggregateFunction)`max(<AttributeName att>)`, map[str,str] attributes, CheckFunctions cf) {
  if ("<att>" notin attributes) {
    cf.addMessage(error("\'<att>\' not part of relation", att@\loc));
  }
}
void check(e:(AggregateFunction)`avg(<AttributeName att>)`, map[str,str] attributes, CheckFunctions cf) {
  if ("<att>" notin attributes) {
    cf.addMessage(error("\'<att>\' not part of relation", att@\loc));
  }
}

void check((Criteria)`( <Criteria cr> )`, map[str,str] attributes, CheckFunctions cf) { check(cr, attributes, cf); } 
void check((Criteria)`not <Criteria cr>`, map[str,str] attributes, CheckFunctions cf) { check(cr, attributes, cf); } 
void check((Criteria)`<CriteriaExpr lhs> = <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); }
void check((Criteria)`<CriteriaExpr lhs> != <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); }
void check((Criteria)`<Criteria lhs> && <Criteria rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); }
void check((Criteria)`<Criteria lhs> || <Criteria rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((Criteria)`<CriteriaExpr lhs> \< <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((Criteria)`<CriteriaExpr lhs> \<= <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((Criteria)`<CriteriaExpr lhs> \> <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((Criteria)`<CriteriaExpr lhs> \>= <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 

void check(c:(CriteriaExpr)`<AttributeName att>`, map[str,str] attributes, CheckFunctions cf) {
  if ("<att>" notin attributes) {
    cf.addMessage(error("Attribute \'<att>\' not part of relation", c@\loc));
  }
}
void check((CriteriaExpr)`<Literal l>`, map[str,str] attributes, CheckFunctions cf) {} 
void check((CriteriaExpr)`( <CriteriaExpr expr> )`, map[str,str] attributes, CheckFunctions cf) { check(expr, attributes, cf); }
void check((CriteriaExpr)`<Criteria cond> ? <CriteriaExpr thn> : <CriteriaExpr els>`, map[str,str] attributes, CheckFunctions cf) { check(cond, attributes, cf); check(thn, attributes, cf); check(els, attributes, cf); }

void check((CriteriaExpr)`| <CriteriaExpr expr> |`, map[str,str] attributes, CheckFunctions cf) { check(expr, attributes, cf); }
void check((CriteriaExpr)`- <CriteriaExpr expr>`, map[str,str] attributes, CheckFunctions cf) { check(expr, attributes, cf); }
//void check((CriteriaExpr)`<CriteriaExpr base>^<CriteriaExpr expo>`, map[str,str] attributes, CheckFunctions cf) { check(base, attributes, cf); check(expo, attributes, cf); } 
void check((CriteriaExpr)`<CriteriaExpr lhs> * <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((CriteriaExpr)`<CriteriaExpr lhs> / <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((CriteriaExpr)`<CriteriaExpr lhs> % <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((CriteriaExpr)`<CriteriaExpr lhs> + <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((CriteriaExpr)`<CriteriaExpr lhs> - <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 

void check((CriteriaExpr)`max(<CriteriaExpr a>,<CriteriaExpr b>)`, map[str,str] attributes, CheckFunctions cf) { check(a, attributes, cf); check(b, attributes, cf); } 
void check((CriteriaExpr)`min(<CriteriaExpr a>,<CriteriaExpr b>)`, map[str,str] attributes, CheckFunctions cf) { check(a, attributes, cf); check(b, attributes, cf); } 

void check((CriteriaExpr)`length(<CriteriaExpr expr>)`, map[str,str] attributes, CheckFunctions cf) { check(expr, attributes, cf); } 
void check((CriteriaExpr)`toInt(<CriteriaExpr expr>)`, map[str,str] attributes, CheckFunctions cf) { check(expr, attributes, cf); } 
void check((CriteriaExpr)`toStr(<CriteriaExpr expr>)`, map[str,str] attributes, CheckFunctions cf) { check(expr, attributes, cf); } 
void check((CriteriaExpr)`<CriteriaExpr lhs> ++ <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((CriteriaExpr)`substr(<CriteriaExpr expr>,<CriteriaExpr offset>,<CriteriaExpr length>)`, map[str,str] attributes, CheckFunctions cf) { check(expr, attributes, cf); check(offset, attributes, cf); ; check(length, attributes, cf);} 

void check((Literal)`<IntLit i>`, map[str,str] attributes, CheckFunctions cf) {}
void check((Literal)`<StrLit s>`, map[str,str] attributes, CheckFunctions cf) {}
void check((Literal)`'<Idd i>'`, map[str,str] attributes, CheckFunctions cf) {}
