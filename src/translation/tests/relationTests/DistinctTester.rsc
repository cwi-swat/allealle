module translation::tests::relationTests::DistinctTester

import translation::Relation;
import translation::AST;

import smtlogic::Core;
import smtlogic::Ints;

import solver::backend::z3::SolverRunner;

import List;
import Relation;

bool checkAllDistinct(Relation r) {
  set[str] nonIdAtts = {att | str att <- r.heading, r.heading[att] != id()};
  if (nonIdAtts == {}) {
    // there are no attributes that can have open values in this relation so the relation must be distinct
    return true;
  }
  
  IndexedRows indexed = index(r);
  
  Formula isDistinct = \true();
    
  for (Tuple key <- indexed.indexedRows<0>, size(indexed.indexedRows[key]) > 1) {
    for (Row row1 <- indexed.indexedRows[key]) {
      isDistinct = \and(isDistinct, \and(row1.constraints.exists, row1.constraints.attConstraints));

      Formula equalRows = \false();
      for (Row row2 <- indexed.indexedRows[key], row2 != row1) {
        Formula attEqual = \true();

        for (str att <- row2.values, att in nonIdAtts) {
          if (term(lhs) := row1.values[att], term(rhs) := row2.values[att]) {
            attEqual = \and(attEqual, equal(lhs, rhs));
          } else {
            throw "Attribute \'<att>\' is not a term? Should not happen";
          }         
        }
        
        equalRows = \or(equalRows, attEqual); 
      }
      
      isDistinct = \and(isDistinct, equalRows);
    }    
  }
  
  str smt = "<declareBoolVars(r)>
            '<declareIntVars(r)>
            '(assert 
            '  <compile(isDistinct)>
            ')";
            
  pid = startSolver();              
  bool sat = isSatisfiable(pid, smt);
  stopSolver(pid);
 
  return !sat;
}

set[str] getBoolVars(Relation r) = {v | /pvar(str v) := r};
set[str] getIntVars(Relation r) = {v | /var(str v, Sort::\int()) := r};

str declareBoolVars(Relation r) = "<for (str var <- getBoolVars(r)) {>
                                  '(declare-const <var> Bool)<}>";

str declareIntVars(Relation r) = "<for (str var <- getIntVars(r)) {>
                                  '(declare-const <var> Int)<}>";
                                  

str compile(\and(set[Formula] forms))         = "(and <for (f <- forms) {>
                                                '  <compile(f)><}>
                                                ')";

str compile(\or(set[Formula] forms))          = "(or <for (f <- forms) {>
                                                '  <compile(f)><}>
                                                ')";

str compile(\not(Formula f))                  = "(not <compile(f)>)"; 
str compile(ite(Formula c, Term t, Term e))   = "(ite " + compile(c) + " " + compile(t) + " " + compile(e) + ")\n";
str compile(\false())                         = "false"; 
str compile(\true())                          = "true";
str compile(\pvar(name))                      = name; 
str compile(equal(set[Formula] fs))           = "(= <for (Formula f <- fs) {> <compile(f)><}>)"; 
str compile(equal(set[Term] ts))              = "(= <for (Term t <- ts) {> <compile(t)><}>)";

default str compile(Formula f) { throw "Unable to compile <f> to SMT, no SMT compiler available"; }

str compile(lit(Literal l))         = compile(l);
str compile(var(str name, Sort s))  = name;

str compile(\int(int i))            = "<i>";
