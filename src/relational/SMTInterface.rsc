module relational::SMTInterface

import SMTInterface;

import logic::Propositional;
import relational::AST;

import Binder;

import List;
 
SMTInterface getRelationalSMTInterface() = <constructSMTVars, <compileVariableDeclaration, compile>, <getValues, mergeModel, negateVariable>>;

set[SMTVar] constructSMTVars(Environment env) = {<name, relational()> | str relName <- env, Binding b := env[relName], Index idx <- b, idx.theory == relational(), var(str name) := b[idx]};

str compileVariableDeclaration(SMTVar var) = "(declare-const <var.name> Bool)" when var.theory == relational();
default str compileVariableDeclaration(SMTVar var) = "";

str compile(\and(set[Formula] forms), str (Formula) compileAll) = "(and <for (f <- forms) {><compileAll(f)> <}>)";
str compile(\or(set[Formula] forms), str (Formula) compileAll) = "(or <for (f <- forms) {><compileAll(f)> <}>)";
str compile(\not(formula), str (Formula) compileAll) = "(not <compileAll(formula)>)";

str compile(\false(), str (Formula) _) = "false";
str compile(\true(), str (Formula) _)  = "true";

str compile(\var(name), str (Formula) _) = "<name>";

default str compile(relational::AST::Formula _, str (Formula) _) = "";

Model getValues(map[str, str] smtValues, set[SMTVar] smtVars) =
  (var : toFormula(smtValues[var.name]) | SMTVar var <- smtVars, var.name in smtValues, var.theory == relational());
 
Formula toFormula("true") = \true();
Formula toFormula("false") = \false();
default Formula toFormula(str someVal) { throw "Unable to construct Boolean formula with value \'<someVal>\'"; }

Environment mergeModel(Model foundValues, Environment env) {
  return visit(env) {
    case var(str name) => foundValues[<name, relational()>] when <name, relational()> in foundValues
  }
}

str negateVariable(SMTVar var, Model model) = "(not <var.name>)" when var.theory == relational(), \true() :=  model[var];
str negateVariable(SMTVar var, Model model) = "<var.name>" when var.theory == relational(), \false() :=  model[var];
default str negateVariable(SMTVar _, Model _) = "";