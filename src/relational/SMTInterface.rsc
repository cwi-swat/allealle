module relational::SMTInterface

import SMTInterface;

import logic::Propositional;
import relational::AST;

import Binder;

import List;
 
SMTInterface getRelationalSMTInterface() = <constructSMTVars, <compileVariableDeclarations, compile>, <getValues, mergeModel>>;

set[SMTVar] constructSMTVars(Environment env) = {<name, relational()> | str relName <- env, Binding b := env[relName], Index idx <- b, idx.theory == relational(), var(str name) := b[idx]};

str compileVariableDeclarations(SMTVar var) = "(declare-const <var.name> Bool)" when var.theory == relational();

str compile(\and(set[Formula] forms), str (Formula) compileAll) = "(and <("" | "<it> <compileAll(f)>" | f <- forms)>)";
str compile(\or(set[Formula] forms), str (Formula) compileAll) = "(or <("" | "<it> <compileAll(f)>" | f <- forms)>)";
str compile(\not(formula), str (Formula) compileAll) = "(not <compileAll(formula)>)";

str compile(\false(), str (Formula) _) = "false";
str compile(\true(), str (Formula) _)  = "true";

str compile(\var(name), str (Formula) _) = "<name>";


Model getValues(map[str, str] smtValues, set[SMTVar] smtVars) =
  (var : toFormula(smtValues[var.name]) | SMTVar var <- smtVars, var.name in smtValues);
 
Formula toFormula("true") = \true();
Formula toFormula("false") = \false();
default Formula toFormula(str someVal) { throw "Unable to construct Boolean formula with value \'<someVal>\'"; }

Environment mergeModel(Model foundValues, Environment env) {
  return visit(env) {
    case var(str name) => foundValues[<name, relational()>] when <name, relational()> in foundValues
  }
}