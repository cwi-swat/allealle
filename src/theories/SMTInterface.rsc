module theories::SMTInterface

import theories::AST;
import theories::Binder;
import logic::Propositional;

import util::Maybe;  
import String;

import IO;
import List;

alias Model = map[SMTVar, Formula];
alias SMTVar = tuple[str name, Theory theory];

set[SMTVar] collectSMTVars(Environment env) = {<name, relTheory()> | str varName <- env, RelationMatrix rm := env[varName], Index idx <- rm, var(str name) := rm[idx].relForm} +
                                              {<var, t> | str varName <- env, RelationMatrix rm := env[varName], Index idx <- rm, Theory t <- rm[idx].ext, Formula f <- rm[idx].ext[t], /just(str var) := constructExtendedTheoryVar(f)}; 

default Maybe[str] constructExtendedTheoryVar(Formula f) { throw "Unable to construct a variable for formula \'<f>\'"; }

str compileVariableDeclaration(SMTVar var) = "(declare-const <var.name> Bool)" when var.theory == relTheory();

str compile(\and(set[Formula] forms)) = "(and <for (f <- forms) {><compile(f)> <}>)";
str compile(\or(set[Formula] forms))  = "(or <for (f <- forms) {><compile(f)> <}>)";
str compile(\not(formula))            = "(not <compile(formula)>)";
str compile(\false())                 = "false";
str compile(\true())                  = "true";
str compile(\var(name))               = "<name>";

Formula getValue(str smtValue, SMTVar var) = toFormula(smtValue) when var.theory == relTheory();
 
Formula toFormula("true") = \true();
Formula toFormula("false") = \false();
default Formula toFormula(str someVal) { throw "Unable to construct Boolean formula with value \'<someVal>\'"; }

Formula mergeModel(Model foundValues, var(str name)) = foundValues[<name, relTheory()>] when <name, relTheory()> in foundValues;

str negateVariable(SMTVar var, \true()) = "(not <var.name>)" when var.theory == relTheory();
str negateVariable(SMTVar var, \false()) = "<var.name>" when var.theory == relTheory();
default Maybe[SMTVar] constructSMTVar(Formula f) { throw "Unable to construct SMT variable for formula <f>, no SMT variable constructor available"; }

str compileSMTVariableDeclarations(set[SMTVar] vars) = ("" | "<it>\n<compileVariableDeclaration(var)>" | SMTVar var <- vars);

default str compileVariableDeclaration(SMTVar var) { throw "Unable to compile variable <var> to SMT, no SMT compiler available"; }

str compileAssert(Formula f) = "(assert <compile(f)>)";
default str compile(Formula f) { throw "Unable to compile <f> to SMT, no SMT compiler available"; }

Model getValues(str smtResult, set[SMTVar] vars) {
  map[str,str] rawSmtVals = (() | it + (var:val) | /(<var:[A-Za-z_0-9]+> <val:[^(^)]+>)/ := substring(smtResult, 1, size(smtResult)-1));
  Model m = (var : form | str varName <- rawSmtVals, SMTVar var:<varName, Theory _> <- vars, Formula form := getValue(rawSmtVals[varName], var));
  
  return m;
} 

default Formula getValue(str smtValue, SMTVar var) { throw "Unable to get the value for SMT value <smtValue>"; }

default str negateVariable(SMTVar v, Formula f) { throw "Unable to negate variable <v> with current value <f>, no SMT negator available"; }

Environment merge(Model foundModel, Environment environment) {
  return visit(environment) {
    case Formula f => mergeModel(foundModel, f)
  } 
}


Formula mergeModel(Model _, \true()) = \true();
Formula mergeModel(Model _, \false()) = \false();
default Formula mergeModel(Model foundValues, Formula f) { throw "Unable to merge model for formula <f>, no SMT merger available";}