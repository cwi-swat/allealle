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
  | atomWithAttributes(Atom name, list[ModelAttribute] attributes)
  ;

data ModelAttribute
  = fixedAttribute(str name, Theory theory, Value val)
  | varAttribute(str name, Theory theory, Value val)
  ;

data Relation 
  = unary(str name, set[VectorAndVar] relation, bool inBaseProblem)
  | nary(str name, set[VectorAndVar] relation, bool inBaseProblem)
  ;
    
data Model 
  = model(set[ModelAtom] visibleAtoms, set[Relation] relations)
  | empty()
  ;

set[SMTVar] collectSMTVars(set[AtomDecl] atoms, Environment env)  {
  set[SMTVar] result = {};

  for (atomWithAttributes(Atom a, list[Attribute] attributes) <- atoms, Attribute at <- attributes) {
    result += constructAtomVar(a, at);
  } 
  
  for (str varName <- env.relations, RelationMatrix m := env.relations[varName], Index idx <- m) {
    if (var(str name) := m[idx].relForm) {
      result += <name, relTheory()>;
    }
    
    //for (int i <- m[idx], str name <- raa.att[idx][i], AttributeFormula attForm <- raa.att[idx][i][name]) {
    //  result += constructAttributeVar(attForm);
    //}
  }
  
  return result;
}

default tuple[str, Theory] constructAtomVar(Atom a, Attribute at) { throw "Unable to construct a variable for atom \'<a>\' and attribute \'<at.name>\'"; } 
//default tuple[str, Theory] constructAttributeVar(AttributeFormula f) { throw "Unable to construct a variable for formula \'<f>\'"; } 

str compileSMTVariableDeclarations(set[SMTVar] vars) = "<for (SMTVar var <- vars) {>
                                                       '<compileVariableDeclaration(var)><}>"; //("" | "<it>\n<compileVariableDeclaration(var)>" | SMTVar var <- vars);
str compileVariableDeclaration(SMTVar var) = "(declare-const <var.name> Bool)" when var.theory == relTheory();
default str compileVariableDeclaration(SMTVar var) { throw "Unable to compile variable <var> to SMT, no SMT compiler available"; }

str compileAttributeValues(list[AtomDecl] atomDecls) = "\n(assert
                                                       '  (and <for (str s <- smt, s != "") {>
                                                       '    <s><}>
                                                       '  )
                                                       ')"
  when list[str] smt := [av | atomWithAttributes(Atom a, list[Attribute] atts) <- atomDecls, Attribute at <- atts, str av := compileAttributeValue(a, at), av != ""],
       smt != [];
                                        
default str compileAttributeValues(list[AtomDecl] atomDecls) = "";

default str compileAttributeValue(Atom a, Attribute at) = "";

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
                               
str compileAdditionalCommands(list[Command] commands) = "<for (Command c <- commands) {>
                                                             '<compileCommand(c)><}>";                               

default str compileCommand(Command c) { throw "Unable to compile command \'<c>\'. No compile function defined.";}

SMTModel getValues(str smtResult, set[SMTVar] vars) {
  SmtValues foundValues = [SmtValues]"<smtResult>"; 
  map[str,SmtValue] rawSmtVals = (() | it + ("<varAndVal.name>":varAndVal.val) | VarAndValue varAndVal <- foundValues.values);

  SMTModel m = (var : form | str varName <- rawSmtVals, SMTVar var:<varName, Theory _> <- vars, Formula form := getValue(rawSmtVals[varName], var));
  
  return m;
}   

Formula toFormula((SmtValue)`true`) = \true();
Formula toFormula((SmtValue)`false`) = \false();
default Formula toFormula(SmtValue someVal) { throw "Unable to construct Boolean formula with value \'<someVal>\'"; }

Formula getValue(SmtValue smtValue, SMTVar var) = toFormula(smtValue) when var.theory == relTheory();
default Formula getValue(SmtValue smtValue, SMTVar var) { throw "Unable to get the value for SMT value \'<smtValue>\', for variable <var>"; }

str negateVariable(str var, \true()) = "(not <var>)";
str negateVariable(str var, \false()) = var;

default str negateVariable(str v, Formula f) { throw "Unable to negate variable <v> with current value <f>"; }
default str negateAttribute(Atom a, ModelAttribute at) { throw "Unable to negate atom\'s \'<a>\' attribute \'<at.name>\', no negation function found"; } 

Model constructModel(SMTModel smtModel, Universe uni, Environment env) { 
  AtomDecl findAtomDecl(Atom a) = ad when AtomDecl ad <- uni.atoms, ad.atom == a;
  
  set[AtomDecl] visibleAtoms = {};
  set[Relation] relations = {};
  
  for (str relName <- env.relations, !startsWith(relName, "_")) {
    set[VectorAndVar] relTuples = {};
    RelationMatrix m = env.relations[relName];
     
    for (Index idx <- m) {
      // all the atoms referenced in the vector should be visible
      if (var(str name) := m[idx].relForm, smtModel[<name, relTheory()>] == \true() ) {
        visibleAtoms += {findAtomDecl(a) | Atom a <- idx};
        relTuples += {vectorAndVar(idx,  name)};
      }
      else if (\true() := m[idx].relForm) {
        visibleAtoms += {findAtomDecl(a) | Atom a <- idx};
        relTuples += {vectorOnly(idx)};        
      } 
    }
    
    if (size(getOneFrom(m)) == 1) {
      relations += {unary(relName, relTuples, relName in env.relations)};
    } else {
      relations += {nary(relName, relTuples, relName in env.relations)};
    } 
  }
  
  list[ModelAttribute] convertAttributes(Atom a, list[Attribute] origAtt) {
    list[ModelAttribute] atts = [];
    
    visit(origAtt) {
      case attribute(str name, Theory t): atts += varAttribute(name, t, findAttributeValue(a, name, t, smtModel));
      case attributeAndValue(str name, Theory t, Value v): atts += fixedAttribute(name, t, v);
    }
    
    return atts;
  }
  
  // Now make sure that visible atoms which hold variables in other theories get their values set
  set[ModelAtom] atomsInModel = {};
  visit (visibleAtoms) {
    case atomOnly(Atom a): atomsInModel += atom(a);
    case atomWithAttributes(Atom a, list[Attribute] attributes): atomsInModel += atomWithAttributes(a, convertAttributes(a, attributes));
  };   

  return model(atomsInModel, relations);
} 

default Value findAttributeValue(Atom a, str name, Theory t, SMTModel smtModel) { throw "Unable to find attribute value for attribute \'<name>\' on atom <a> with theory \'<t>\'";}