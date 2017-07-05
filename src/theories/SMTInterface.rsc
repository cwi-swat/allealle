module theories::SMTInterface

import theories::AST;
import theories::Binder;
import logic::Propositional;

import util::Maybe;  
import String;

import IO;
import List;
import Map;

import theories::SMTValueSyntax;

alias SMTVar = tuple[str name, Theory theory];
alias SMTModel = map[SMTVar, Formula];

data VectorAndVar 
  = vectorAndVar(list[Atom] vector, str smtVarName)
  | vectorOnly(list[Atom] vector) 
  ;

data ModelAtom
  = atom(Atom name)
  | varAtom(Atom name, Theory theory, AtomValue val)
  | fixedAtom(Atom name, Theory theory, AtomValue val)
  ;

data Relation 
  = unary(str name, set[VectorAndVar] relation, bool inBaseProblem)
  | nary(str name, set[VectorAndVar] relation, bool inBaseProblem)
  ;
    
data Model 
  = model(set[ModelAtom] visibleAtoms, set[Relation] relations)
  | empty()
  ;

set[SMTVar] collectSMTVars(Universe uni, Environment env)  {
  set[SMTVar] result = {};

  for (AtomDecl ad <- uni.atoms, ad has theory, /just(tuple[str var, Theory t] r) := constructExtendedTheoryVar(ad)) {
    result += <r.var, r.t>;
  }
  
  for (str varName <- env, RelationMatrix rm := env[varName], Index idx <- rm) {
    if (var(str name) := rm[idx].relForm) {
      result += <name, relTheory()>;
    }
    
    for (int i <- rm[idx].ext, just(tuple[str var, Theory t] r) := constructExtendedTheoryVar(rm[idx].ext[i])) {
      result += <r.var, r.t>;
    }
  }

  return result;
}
  //= {<name, relTheory()> | str varName <- env, RelationMatrix rm := env[varName], Index idx <- rm, var(str name) := rm[idx].relForm} +
  //  {<r.var, r.t> | str varName <- env, RelationMatrix rm := env[varName], Index idx <- rm, int i <- rm[idx].ext, /just(tuple[str var, Theory t] r) := constructExtendedTheoryVar(rm[idx].ext[i])} +
  //  {<r.var, r.t> | AtomDecl ad <- uni.atoms, ad has theory, /just(tuple[str var, Theory t] r) := constructExtendedTheoryVar(ad)}; 

default Maybe[tuple[str, Theory]] constructExtendedTheoryVar(AtomDecl ad) { throw "Unable to construct a variable for atom declaration \'<ad>\'"; }
default Maybe[tuple[str, Theory]] constructExtendedTheoryVar(set[TheoryFormula] f) { throw "Unable to construct a variable for formula \'<f>\'"; } 

str compileSMTVariableDeclarations(set[SMTVar] vars) = "<for (SMTVar var <- vars) {>
                                                       '<compileVariableDeclaration(var)><}>"; //("" | "<it>\n<compileVariableDeclaration(var)>" | SMTVar var <- vars);
str compileVariableDeclaration(SMTVar var) = "(declare-const <var.name> Bool)" when var.theory == relTheory();
default str compileVariableDeclaration(SMTVar var) { throw "Unable to compile variable <var> to SMT, no SMT compiler available"; }

str compileAtomExpressions(list[AtomDecl] atomDecls) = "\n(assert
                                                       '  (and <for (str s <- smt) {>
                                                       '    <s><}>
                                                       '  )
                                                       ')"
  when list[str] smt := [s | AtomDecl ad <- atomDecls, str s := compileAtomValueExpr(ad), s != ""],
       smt != [];                                      

default str compileAtomExpressions(list[AtomDecl] atomDecls) = "";

default str compileAtomValueExpr(AtomDecl _) = "";                                                       

str compile(\and(set[Formula] forms)) = "(and <for (f <- forms) {> 
                                                    '  <compile(f)><}>)";
str compile(\or(set[Formula] forms))  = "(or <for (f <- forms) {>
                                                   '  <compile(f)><}>)";
str compile(\not(formula))            = "(not <compile(formula)>)";
//str compile(ite(Formula c, Formula t, Formula e)) = "(ite 
//                                                    '  <compile(c)>
//                                                    '  <compile(t)>
//                                                    '  <compile(e)>
//                                                    ')";                                                      
str compile(\false())                 = "false"; 
str compile(\true())                  = "true";
str compile(\var(name))               = name; 

default str compile(Formula f) { throw "Unable to compile <f> to SMT, no SMT compiler available"; }

str compileAssert(Formula f) = "\n(assert 
                               '  <compile(f)>
                               ')"; 

SMTModel getValues(str smtResult, set[SMTVar] vars) {
  Values foundValues = [Values]"<smtResult>"; 
  map[str,Value] rawSmtVals = (() | it + ("<varAndVal.name>":varAndVal.val) | VarAndValue varAndVal <- foundValues.values);

  SMTModel m = (var : form | str varName <- rawSmtVals, SMTVar var:<varName, Theory _> <- vars, Formula form := getValue(rawSmtVals[varName], var));
  
  return m;
}   

Formula toFormula((Value)`true`) = \true();
Formula toFormula((Value)`false`) = \false();
default Formula toFormula(Value someVal) { throw "Unable to construct Boolean formula with value \'<someVal>\'"; }

Formula getValue(Value smtValue, SMTVar var) = toFormula(smtValue) when var.theory == relTheory();
default Formula getValue(Value smtValue, SMTVar var) { throw "Unable to get the value for SMT value <smtValue>"; }

str negateVariable(str var, \true()) = "(not <var>)";
str negateVariable(str var, \false()) = var;
default str negateVariable(str v, Formula f) { throw "Unable to negate variable <v> with current value <f>"; }

default str negateAtomVariable(ModelAtom ad) { throw "Unable to negate atom variable \'<ad.name>\', no negation function found"; } 

Model constructModel(SMTModel smtModel, Universe uni, Environment env) { 
  AtomDecl findAtomDecl(Atom a) = ad when AtomDecl ad <- uni.atoms, ad.atom == a;
  
  set[AtomDecl] visibleAtoms = {};
  set[Relation] relations = {};
  
  for (str relName <- env, !startsWith(relName, "_")) {
    set[VectorAndVar] relTuples = {};
     
    for (Index idx <- env[relName]) {
      // all the atoms referenced in the vector should be visible
      if (<var(str name), ExtensionEncoding _> := env[relName][idx], smtModel[<name, relTheory()>] == \true() ) {
        visibleAtoms += {findAtomDecl(a) | Atom a <- idx};
        relTuples += {vectorAndVar(idx,  name)};
      }
      else if (<\true(), ExtensionEncoding _> := env[relName][idx]) {
        visibleAtoms += {findAtomDecl(a) | Atom a <- idx};
        relTuples += {vectorOnly(idx)};        
      } 
    }
    
    if (size(getOneFrom(env[relName])) == 1) {
      relations += {unary(relName, relTuples, relName in env)};
    } else {
      relations += {nary(relName, relTuples, relName in env)};
    } 
  }
  
  // Now make sure that visible atoms which hold variables in other theories get their values set
  set[ModelAtom] atomsInModel = {};
  visit (visibleAtoms) {
    case atomOnly(Atom a): atomsInModel += atom(a);
    case atomAndTheory(Atom a, Theory t): atomsInModel += varAtom(a, t, findAtomValue(a, t, smtModel));
    case atomTheoryAndValue(Atom a, Theory t, AtomValue val): atomsInModel += fixedAtom(a, t, val);
  };   

  return model(atomsInModel, relations);
} 

default AtomValue findAtomValue(Atom a, Theory t, SMTModel smtModel) { throw "Unable to find atom value for atom <a> with theory \'<t>\'";}