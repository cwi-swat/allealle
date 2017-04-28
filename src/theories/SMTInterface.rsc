module theories::SMTInterface

import theories::AST;
import theories::Binder;
import logic::Propositional;

import util::Maybe;  
import String;

import IO;
import List;

import theories::SMTValueSyntax;

alias Model = map[SMTVar, Formula];
alias SMTVar = tuple[str name, Theory theory];

set[SMTVar] collectSMTVars(Environment env) = {<name, relTheory()> | str varName <- env, RelationMatrix rm := env[varName], Index idx <- rm, var(str name) := rm[idx].relForm} +
                                              {<var, t> | str varName <- env, RelationMatrix rm := env[varName], Index idx <- rm, Theory t <- rm[idx].ext, int i <- rm[idx].ext[t], /just(str var) := constructExtendedTheoryVar(rm[idx].ext[t][i])}; 

default Maybe[str] constructExtendedTheoryVar(Formula f) { throw "Unable to construct a variable for formula \'<f>\'"; }

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

Model getValues(str smtResult, set[SMTVar] vars) {
  Values foundValues = [Values]"<smtResult>"; 
  map[str,Value] rawSmtVals = (() | it + ("<varAndVal.name>":varAndVal.val) | VarAndValue varAndVal <- foundValues.values);
  
  Model m = (var : form | str varName <- rawSmtVals, SMTVar var:<varName, Theory _> <- vars, Formula form := getValue(rawSmtVals[varName], var));
  
  return m;
}   

Formula toFormula((Value)`true`) = \true();
Formula toFormula((Value)`false`) = \false();
default Formula toFormula(Value someVal) { throw "Unable to construct Boolean formula with value \'<someVal>\'"; }

Formula getValue(Value smtValue, SMTVar var) = toFormula(smtValue) when var.theory == relTheory();
default Formula getValue(Value smtValue, SMTVar var) { throw "Unable to get the value for SMT value <smtValue>"; }

str negateVariable(SMTVar var, \true(), relTheory()) = "(not <var.name>)";
str negateVariable(SMTVar var, \false(), relTheory()) = var.name;
default str negateVariable(SMTVar v, Formula f, Theory t) { throw "Unable to negate variable <v> with current value <f> for theory <t>, no SMT negator available"; }

Environment merge(Model foundModel, Environment environment) { 
  return visit(environment) {
    case Formula f => mergeModel(foundModel, f)
  } 
} 
 
Formula mergeModel(Model foundValues, var(str name)) = foundValues[<name, relTheory()>] when <name, relTheory()> in foundValues;

Formula mergeModel(Model _, \true()) = \true();
Formula mergeModel(Model _, \false()) = \false();
default Formula mergeModel(Model foundValues, Formula f) { throw "Unable to merge model for formula <f>, no SMT merger available";}