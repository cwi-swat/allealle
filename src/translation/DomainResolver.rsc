module translation::DomainResolver

import translation::Syntax;

import ParseTree;
import IO;

alias ResolvedDomains = map[loc,translation::Syntax::Domain];

ResolvedDomains resolveDomains(Problem p) {
  //map[str,Domain] attr = resolveAttributes(p);
  //
  //ResolvedDomains resolvedDomains = ();
  //bool addDomain(loc exprLoc, Domain d) {
  //  resolvedDomains[exprLoc] = d;
  //  return true;
  //}
  //Domain getDomain(loc exprLoc) {
  //  if (exprLoc in resolvedDomains) {
  //    return resolvedDomains[exprLoc];
  //  } 
  //   
  //  throw "Domain not yet resolved for \'<exprLoc>\'";
  //}   
  //
  //bottom-up visit(p) {
  //  case AlleExpr e: resolveDomain(e, attr, getDomain, addDomain);
  //}
  //
  //return resolvedDomains;   
  return ();
} 

//map[str,Domain] resolveAttributes(Problem p) =
// ("<name>": dom | (Relation)`<Variable _> (<Arity _>::<{AttributeHeader ","}+ headers>) <RelationalBound _>` <- p.relations, (AttributeHeader)`<AttributeName name>:<Domain dom>` <- headers);
//
//@memo
//Domain ID() = (Domain)`id`;
//
//@memo
//Domain FAIL() = (Domain)`FAIL`;
//
//bool resolveDomain(e:(AlleExpr)`( <AlleExpr expr> )`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, getDomain(expr@\loc));  
//
//bool resolveDomain(e:(AlleExpr)`<Variable _>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, ID());
//bool resolveDomain(e:(AlleExpr)`<AlleExpr _>::<AttributeName name>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, attributeDomains["<name>"])
//  when "<name>" in attributeDomains; 
//
//bool resolveDomain(e:(AlleExpr)`<AlleExpr lhs>.<AlleExpr rhs>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, ID())
//  when ID() == getDomain(lhs@\loc),
//       ID() == getDomain(rhs@\loc);
//       
//bool resolveDomain(e:(AlleExpr)`~<AlleExpr expr>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, ID())
//  when ID() == getDomain(expr@\loc);
//       
//bool resolveDomain(e:(AlleExpr)`^<AlleExpr expr>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, ID())
//  when ID() == getDomain(expr@\loc); 
//  
//bool resolveDomain(e:(AlleExpr)`*<AlleExpr expr>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, ID())
//  when ID() == getDomain(expr@\loc);
//  
//bool resolveDomain(e:(AlleExpr)`<AlleExpr lhs> + <AlleExpr rhs>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, ID())
//  when ID() == getDomain(lhs@\loc),
//       ID() == getDomain(rhs@\loc);
//       
//bool resolveDomain(e:(AlleExpr)`<AlleExpr lhs> ++ <AlleExpr rhs>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, ID())
//  when ID() == getDomain(lhs@\loc),
//       ID() == getDomain(rhs@\loc);
//        
//bool resolveDomain(e:(AlleExpr)`<AlleExpr lhs> & <AlleExpr rhs>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, ID())
//  when ID() == getDomain(lhs@\loc),
//       ID() == getDomain(rhs@\loc);
//
//bool resolveDomain(e:(AlleExpr)`<AlleExpr lhs> \\ <AlleExpr rhs>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, ID())
//  when ID() == getDomain(lhs@\loc),
//       ID() == getDomain(rhs@\loc);
//       
//bool resolveDomain(e:(AlleExpr)`<AlleExpr lhs> -\> <AlleExpr rhs>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, ID())
//  when ID() == getDomain(lhs@\loc),
//       ID() == getDomain(rhs@\loc); 
//       
//bool resolveDomain(e:(AlleExpr)`<AlleFormula form> ? <AlleExpr then> : <AlleExpr \else>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, ID())
//  when ID() == getDomain(then@\loc),
//       ID() == getDomain(\else@\loc);
//        
//bool resolveDomain(e:(AlleExpr)`{ <{VarDeclaration ","}+ decls> | <AlleFormula form> }`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, ID());      
//
//default bool resolveDomain(AlleExpr e, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) = addDomain(e@\loc, FAIL());
