module translation::SMTInterface

import translation::AST;
import translation::Binder;
import translation::SMTValueSyntax;

import logic::Propositional;

import util::Maybe;  
import String;

import IO;
import List;
import Map;

alias SMTVar = tuple[str name, Domain domain];
alias SMTModel = map[SMTVar, Formula];

data ModelAttribute
  = fixedAttribute(str name, Domain dom, Value val)
  | varAttribute(str name, Domain dom, Value val, str smtVarName)
  ;

data ModelIndex
  = fixedIndex(Index idx)
  | varIndex(Index idx, str smtVarName)
  ;
  
data ModelTuple
  = mTuple(ModelIndex idx, list[ModelAttribute] attributes)
  ;  

data ModelRelation 
  = unary(str name, set[ModelTuple] tuples)
  | nary(str name, set[ModelTuple] tuples)
  ;
    
data Model 
  = model(set[ModelRelation] relations)
  | empty()
  ;

set[SMTVar] collectSMTVars(Environment env)  {
  set[SMTVar] result = {};

  for (str varName <- env.relations, RelationMatrix m := env.relations[varName], Index idx <- m, var(str name) := m[idx].relForm) {
      result += <name, id()>;
  }    
    
  for (Index idx <- env.attributes, str attName <- env.attributes[idx], just(SMTVar var) := constructAttributeVar(env.attributes[idx][attName])) {
    result += var;
  }
  
  return result;
}

set[SMTVar] collectIntermediateSMTVars(set[Formula] intermediates) = {v | Formula f <- intermediates, just(SMTVar v) := constructAttributeVar(f)};

default Maybe[SMTVar] constructAttributeVar(Formula f) { throw "Unable to construct a variable for formula \'<f>\'"; } 

str compileSMTVariableDeclarations(set[SMTVar] vars) = "<for (SMTVar var <- vars) {>
                                                       '<compileVariableDeclaration(var)><}>";

str compileVariableDeclaration(<str name, id()>) = "(declare-const <name> Bool)";
default str compileVariableDeclaration(SMTVar var) { throw "Unable to compile variable <var> to SMT, no SMT compiler available for theory \'<var.domain>\'"; }

str compile(\and(set[Formula] forms)) {
   str clauses = "";
   for (f <- forms) {
    clauses += compile(f) + " ";
   }
   
   return "(and " + clauses + ")\n";
}   
str compile(\or(set[Formula] forms))  { 
   str clauses = "";
   for (f <- forms) {
    clauses += compile(f) + " ";
   }
   
   return "(or " + clauses + ")\n";
}

str compile(\not(formula))            = "(not " + compile(formula) + ")";
str compile(ite(Formula c, Formula t, Formula e)) = "(ite " + compile(c) + " " + compile(t) + " " + compile(e) + ")\n";
                                                                                                         
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

  SMTModel m = (var : form | str varName <- rawSmtVals, SMTVar var:<varName, Domain _> <- vars, Formula form := getValue(rawSmtVals[varName], var));
  
  return m;
}   

Formula toFormula((SmtValue)`true`) = \true();
Formula toFormula((SmtValue)`false`) = \false();
default Formula toFormula(SmtValue someVal) { throw "Unable to construct Boolean formula with value \'<someVal>\'"; }

Formula getValue(SmtValue smtValue, <str _, id()>) = toFormula(smtValue);
default Formula getValue(SmtValue smtValue, SMTVar var) { throw "Unable to get the value for SMT value \'<smtValue>\', for variable <var>"; }

str negateVariable(str var, \true()) = "(not <var>)";
str negateVariable(str var, \false()) = var;

default str negateVariable(str v, Formula f) { throw "Unable to negate variable <v> with current value <f>"; }

Model constructRelationalModel(SMTModel smtModel, Environment env) { 
  set[ModelRelation] relations = {};
  
  for (str relName <- env.relations) {
    set[ModelTuple] tuples = {};
    RelationMatrix m = env.relations[relName];
     
    for (Index idx <- m, !(var(str n) := m[idx].relForm && smtModel[<n, id()>] == \false())) {
      ModelIndex mIdx;
      list[ModelAttribute] attributes = [];
      
      if (var(str name) := m[idx].relForm, smtModel[<name, id()>] == \true() ) {
        mIdx = varIndex(idx, name);
      }
      else if (\true() := m[idx].relForm) {
        mIdx = fixedIndex(idx);
      }  
      
      if (idx in env.attributes) {
        for (str attName <- env.attributes[idx]) {
          tuple[Domain attDom, Value attVal] val = getAttributeValue(env.attributes[idx][attName], smtModel);
          
          if (just(str smtVarName) := getAttributeVarName(env.attributes[idx][attName])) {
            attributes += varAttribute(attName, val.attDom, val.attVal, smtVarName);
          } else {
            attributes += fixedAttribute(attName, val.attDom, val.attVal); 
          }     
        }  
      }
      
      tuples += mTuple(mIdx, attributes); 
    }
    
    if (size(getOneFrom(env.relations[relName])) == 1) {
      relations += unary(relName, tuples);
    } else {
      relations += nary(relName, tuples);
    }  
  }
  
  return model(relations);
} 

default Maybe[str] getAttributeVarName(Formula attForm) { throw "Unable to check what the var name is of attribute with value \'<attForm>\' "; }
default tuple[Domain, Value] getAttributeValue(Formula attForm, SMTModel _) { throw "Unable to find attribute value for attribute formula \'<attForm>\'";}

default str negateAttribute(Domain dom, str varName, Value currentVal) { throw "Unable to negate \'<varName>\' for domain \'<dom>\', no negation function found"; }