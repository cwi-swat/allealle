module translation::SMTInterface

import translation::AST;
import translation::Relation;
import translation::Environment;
import translation::SMTValueSyntax;

import smtlogic::Core;

import util::Maybe;  
import String;
import IO;
import List;
import Map;

alias SMTVar = tuple[str name, Sort sort];
alias SMTModel = map[SMTVar, Term];

data ModelAttribute
  = idAttribute(str name, str id)
  | fixedAttribute(str name, Term val)
  | varAttribute(str name, Term val, str smtVarName)
  ;
  
data ModelTuple
  = fixedTuple(list[ModelAttribute] attributes)
  | varTuple(list[ModelAttribute] attributes, str smtVarName)
  ;  

data ModelRelation 
  = mRelation(str name, Heading heading, list[ModelTuple] tuples)
  ;
    
data Model 
  = model(set[ModelRelation] relations)
  | empty()
  ;

set[SMTVar] collectSMTVars(Environment env)  {
  set[SMTVar] result = {};

  for (str varName <- env.relations, Relation r := env.relations[varName], Tuple t <- r.rows) {
    result += {<name, sort> | /var(str name, Sort sort) := t};
    
    if (pvar(str name) := r.rows[t].exists) {
      result += <name, \bool()>;
    }
  }    
    
  return result;
}

str compileSMTVariableDeclarations(set[SMTVar] vars) = "<for (SMTVar var <- vars) {>
                                                       '<compileVariableDeclaration(var)><}>";

str compileVariableDeclaration(<str name, \bool()>) = "(declare-const <name> Bool)";
default str compileVariableDeclaration(SMTVar var) { throw "Unable to compile variable <var> to SMT, no SMT compiler available for sort \'<var.sort>\'"; }

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

str compilt(ttrue())                = "true";
str compilt(ffalse())               = "false";
str compile(id(str i))              { throw "Unable to compile id \'<i>\' to SMT"; }

str compileAssert(Formula f) = "\n(assert 
                               '  <compile(f)>
                               ')"; 
                                 
str compileCommands(list[Command] commands) = "<for (Command c <- commands) {>
                                                             '<compileCommand(c)><}>";                               

default str compileCommand(Command c) { throw "Unable to compile command \'<c>\'. No compile function defined.";}

SMTModel getValues(str smtResult, set[SMTVar] vars) {
  SmtValues foundValues = [SmtValues]"<smtResult>"; 
  map[str,SmtValue] rawSmtVals = (() | it + ("<varAndVal.name>":varAndVal.val) | VarAndValue varAndVal <- foundValues.values);

  SMTModel m = (var : val | str varName <- rawSmtVals, SMTVar var:<varName, Sort _> <- vars, Term val := getValue(rawSmtVals[varName], var));
  
  return m;
}    

Term getValue((SmtValue)`true`, <str _, \bool()>) = lit(ttrue());
Term getValue((SmtValue)`false`, <str _, \bool()>) = lit(ffalse());
default Term getValue(SmtValue smtValue, SMTVar var) { throw "Unable to get the value for SMT value \'<smtValue>\', for variable <var>"; }

str negateVariable(str var, lit(ttrue())) = "(not <var>)";
str negateVariable(str var, lit(ffalse())) = var;

default str negateVariable(str v, Term t) { throw "Unable to negate variable <v> with current value <t>"; }

Model constructRelationalModel(SMTModel smtModel, Environment env) { 
  list[ModelAttribute] constructAttributes(Tuple t) {
    list[ModelAttribute] attributes = [];
    for (str att <- t) {
      if (lit(id(str k)) := t[att]) {
        attributes += idAttribute(att,k);
      } else if (l:lit(Literal _) := t[att]) {
        attributes += fixedAttribute(att, l); 
      } else if (v:var(str name, Sort s) := t[att]) {
        attributes += varAttribute(att, smtModel[<name,s>], name);
      }
    } 
     
    return attributes; 
  }
  
  set[ModelRelation] relations = {};
  
  for (str relName <- env.relations) {
    list[ModelTuple] tuples = [];
    Relation r = env.relations[relName];
     
    for (Tuple t <- r.rows) {
      if (r.rows[t].exists == \true()) {
        tuples += fixedTuple(constructAttributes(t));
      } else if (pvar(str name) := r.rows[t].exists && smtModel[<name,\bool()>] == lit(ttrue())) {
        tuples += varTuple(constructAttributes(t), name);
      }
    }
    
    relations += mRelation(relName, env.relations[relName].heading, tuples);
  }
  
  return model(relations);
} 

default str negateAttribute(Domain dom, str varName, Term currentVal) { throw "Unable to negate \'<varName>\' for domain \'<dom>\', no negation function found"; }