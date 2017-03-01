module theories::SMTInterface

import theories::AST;
import theories::Binder;
import logic::Boolean;

import util::Maybe; 
import String;

alias Model = map[SMTVar, Formula];
alias SMTVar = tuple[str name, Theory theory];

set[SMTVar] collectSMTVars(Environment env) = {var | str varName <- env, Binding b := env[varName], Index idx <- b, /just(SMTVar var) := constructSMTVar(b[idx])}; 

Maybe[SMTVar] constructSMTVar(\true()) = nothing();
Maybe[SMTVar] constructSMTVar(\false()) = nothing();
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