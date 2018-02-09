module ide::UnionCompatibilityChecker

import ide::CombinedSyntax;

import ParseTree;
import Message;
import Map;
import IO;

data UnionResult 
  = heading(map[str,str] attributes)
  | incompatible()
  ;
  
alias UnionCompatibilityResult = tuple[map[loc, UnionResult] headings, set[Message] messages];

alias CheckFunctions = tuple[void (loc,UnionResult) add, UnionResult (loc) lookup, void (Message) addMessage];
alias Environment = map[str,UnionResult];
  
UnionCompatibilityResult checkUnionCompatibilty(Problem p) {  
  map[loc,UnionResult] headings = ();
  set[Message] messages = {};
    
  void add(loc l,UnionResult r) {
    headings[l] = r;
  }
  
  UnionResult lookup(loc l) = (l in headings) ? headings[l] : incompatible();
  
  void addMsg(Message m) { messages += m; }
  
  Environment env = buildEnvironment(p);  
  for (AlleFormula f <- p.constraints) {
    check(f,env,<add,lookup,addMsg>);
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
    case (Relation)`<RelVar v> (<{HeaderAttribute ","}+ header>) <RelationalBound bounds>`: env["<v>"] = heading(("<ha.name>":"<ha.dom>()" | HeaderAttribute ha <- header));
  }
  
  return env;
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
  
  if (heading(map[str,str] attributes) := cf.lookup(expr@\loc)) {
    if (renamings<0> - attributes<0> != {}) {
      cf.add(e@\loc, incompatible());
      cf.addMessage(error("Attributes in the renaming do not exists in the relation",e@\loc));       
    } else {
      map[str,str] renamed = ((old in renamings ? renamings[old] : old) : attributes[old] | str old <- attributes);
      if (size(renamed) != size(attributes)) {
        cf.add(e@\loc, incompatible());
        cf.addMessage(error("Renaming collides with existing attributes",e@\loc));       
      } else {
        cf.add(e@\loc, heading(renamed));
      }
    }  
  } else {
    cf.add(e@\loc, incompatible());
  }
}

void check(e:(AlleExpr)`<AlleExpr expr>[<{AttributeName ","}+ atts>]`, Environment env, CheckFunctions cf) {
  check(expr, env, cf);
  
  set[str] projectedAtts = {"<att>" | AttributeName att <- atts};
  if (heading(map[str,str] attributes) := cf.lookup(expr@\loc)) {
   if (projectedAtts & attributes<0> != projectedAtts) {
    cf.add(e@\loc, incompatible());
    cf.addMessage(error("Not all projected attributes are in the relation", e@\loc));
   } else {
    cf.add(e@\loc, heading((a : attributes[a] | str a <- projectedAtts)));
   }
  } else {
    cf.add(e@\loc, incompatible());
  }  
}

void check(e:(AlleExpr)`<AlleExpr expr>[<{AggregateFunctionDef ","}+ aggFuncs>]`, Environment env, CheckFunctions cf) {
  check(expr, env, cf);
  
  if (heading(map[str,str] attributes) := cf.lookup(expr@\loc)) {  
    for (AggregateFunctionDef def <- aggFuncs) {
      check(def, attributes, cf);
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
  
void check(e:(AlleExpr)`~<TupleAttributeSelection tas> <AlleExpr expr>`, Environment env, CheckFunctions cf) { 
  check(expr,env,cf);
  checkTasAgaintsAttributes(e@\loc, expr@\loc, tas, cf);
}
    
void check(e:(AlleExpr)`^<TupleAttributeSelection tas> <AlleExpr expr>`, Environment env, CheckFunctions cf) { 
  check(expr,env,cf);
  checkTasAgaintsAttributes(e@\loc, expr@\loc, tas, cf);
}

void check(e:(AlleExpr)`*<TupleAttributeSelection tas> <AlleExpr expr>`, Environment env, CheckFunctions cf) { 
  check(expr,env,cf);
  checkTasAgaintsAttributes(e@\loc, expr@\loc, tas, cf);
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
      cf.addMessage(error("Relations must have distinct attributes", e@\loc));
    } else {
      cf.add(e@\loc, heading(attLhs + attRhs));
    }
  } else {
    cf.add(e@\loc, incompatible());
  } 
}

void check(e:(AggregateFunctionDef)`<AttributeName bindTo> / <AggregateFunction func>`, map[str,str] attributes, CheckFunctions cf) {
    
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
void check((CriteriaExpr)`| <CriteriaExpr expr> |`, map[str,str] attributes, CheckFunctions cf) { check(expr, attributes, cf); }
void check((CriteriaExpr)`- <CriteriaExpr expr>`, map[str,str] attributes, CheckFunctions cf) { check(expr, attributes, cf); }
void check((CriteriaExpr)`<CriteriaExpr lhs> * <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((CriteriaExpr)`<CriteriaExpr lhs> / <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((CriteriaExpr)`<CriteriaExpr lhs> % <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((CriteriaExpr)`<CriteriaExpr lhs> + <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 
void check((CriteriaExpr)`<CriteriaExpr lhs> - <CriteriaExpr rhs>`, map[str,str] attributes, CheckFunctions cf) { check(lhs, attributes, cf); check(rhs, attributes, cf); } 

void check((Literal)`<IntLit i>`, map[str,str] attributes, CheckFunctions cf) {}
void check((Literal)`'<Idd i>'`, map[str,str] attributes, CheckFunctions cf) {}
