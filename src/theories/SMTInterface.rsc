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

data Relation 
  = unary(str name, set[VectorAndVar] relation)
  | nary(str name, set[VectorAndVar] relation)
  ;
    
data Model 
  = model(set[AtomDecl] visibleAtoms, set[Relation] relations)
  | empty()
  ;

set[SMTVar] collectSMTVars(Universe uni, Environment env) 
  = {<name, relTheory()> | str varName <- env, RelationMatrix rm := env[varName], Index idx <- rm, var(str name) := rm[idx].relForm} +
    {<r.var, r.t> | str varName <- env, RelationMatrix rm := env[varName], Index idx <- rm, int i <- rm[idx].ext, /just(tuple[str var, Theory t] r) := constructExtendedTheoryVar(rm[idx].ext[i])} +
    {<r.var, r.t> | AtomDecl ad <- uni.atoms, ad has theory, /just(tuple[str var, Theory t] r) := constructExtendedTheoryVar(ad)}; 

default Maybe[tuple[str, Theory]] constructExtendedTheoryVar(AtomDecl ad) { throw "Unable to construct a variable for atom declaration \'<ad>\'"; }
default Maybe[tuple[str, Theory]] constructExtendedTheoryVar(set[TheoryFormula] f) { throw "Unable to construct a variable for formula \'<f>\'"; } 

str compileSMTVariableDeclarations(set[SMTVar] vars) = ("" | "<it>\n<compileVariableDeclaration(var)>" | SMTVar var <- vars);
str compileVariableDeclaration(SMTVar var) = "(declare-const <var.name> Bool)" when var.theory == relTheory();
default str compileVariableDeclaration(SMTVar var) { throw "Unable to compile variable <var> to SMT, no SMT compiler available"; }

str compile(\and(set[Formula] forms)) = "(and <for (f <- forms) {> 
                                                    '  <compile(f)><}>)";
str compile(\or(set[Formula] forms))  = "(or <for (f <- forms) {>
                                                   '  <compile(f)><}>)";
str compile(\not(formula))            = "(not <compile(formula)>)";
str compile(ite(Formula c, Formula t, Formula e)) = "(ite 
                                                    '  <compile(c)>
                                                    '  <compile(t)>
                                                    '  <compile(e)>
                                                    ')";                                                      
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

str negateVariable(str var, \true(), relTheory()) = "(not <var>)";
str negateVariable(str var, \false(), relTheory()) = var;
default str negateVariable(str v, Formula f, Theory t) { throw "Unable to negate variable <v> with current value <f> for theory <t>, no SMT negator available"; }

Model constructModel(SMTModel smtModel, Universe uni, Environment env) { 
  AtomDecl findAtomDecl(Atom a) = ad when AtomDecl ad <- uni.atoms, ad.atom == a;
  
  set[AtomDecl] visibleAtoms = {};
  set[Relation] relations = {};
  
  for (str relName <- env) {
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
      relations += {unary(relName, relTuples)};
    } else {
      relations += {nary(relName, relTuples)};
    } 
  }
  
  // Now make sure that visible atoms which hold variables in other theories get their values set
  visibleAtoms = visit(visibleAtoms) {
    case atomAndTheory(Atom a, Theory t) => findAtomValue(a, t, smtModel)
  };   

  return model(visibleAtoms, relations);
} 

default AtomDecl findAtomValue(Atom a, Theory t, SMTModel smtModel) { throw "Unable to find atom value for atom <a> with theory \'<t>\'";}