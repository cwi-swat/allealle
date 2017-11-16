module translation::theories::integer::DomainResolver

extend translation::DomainResolver;

import translation::Syntax;
import translation::theories::integer::Syntax;

import ParseTree;
import IO;

@memo
Domain integer() = (Domain)`int`;


bool resolveDomain(e:(AlleExpr)`<IntLit i>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) 
  = addDomain(e@\loc, integer());
  
bool resolveDomain(e:(AlleExpr)`- <AlleExpr expr>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) 
  = addDomain(e@\loc, integer())
  when getDomain(expr@\loc) == integer();
  
bool resolveDomain(e:(AlleExpr)`|<AlleExpr expr>|`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) 
  = addDomain(e@\loc, integer())
  when getDomain(expr@\loc) == integer();
  
bool resolveDomain(e:(AlleExpr)`<AlleExpr lhs> * <AlleExpr rhs>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) 
  = addDomain(e@\loc, integer())
  when getDomain(lhs@\loc) == integer(),
       getDomain(rhs@\loc) == integer();

bool resolveDomain(e:(AlleExpr)`<AlleExpr lhs> / <AlleExpr rhs>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) 
  = addDomain(e@\loc, integer())
  when getDomain(lhs@\loc) == integer(),
       getDomain(rhs@\loc) == integer();

bool resolveDomain(e:(AlleExpr)`<AlleExpr lhs> % <AlleExpr rhs>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) 
  = addDomain(e@\loc, integer())
  when getDomain(lhs@\loc) == integer(),
       getDomain(rhs@\loc) == integer();
  
bool resolveDomain(e:(AlleExpr)`<AlleExpr lhs> + <AlleExpr rhs>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) 
  = addDomain(e@\loc, integer())
  when getDomain(lhs@\loc) == integer(),
       getDomain(rhs@\loc) == integer();
 
bool resolveDomain(e:(AlleExpr)`<AlleExpr lhs> - <AlleExpr rhs>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) 
  = addDomain(e@\loc, integer())
  when getDomain(lhs@\loc) == integer(),
       getDomain(rhs@\loc) == integer();

bool resolveDomain(e:(AlleExpr)`sum ( <AlleExpr expr> )`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) 
  = addDomain(e@\loc, integer())
  when getDomain(expr@\loc) == integer();  

bool resolveDomain(e:(AlleExpr)`#<AlleExpr expr>`, map[str,Domain] attributeDomains, Domain (loc) getDomain, bool (loc,Domain) addDomain) 
  = addDomain(e@\loc, integer());    