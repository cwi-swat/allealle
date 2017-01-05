module integer::SMTInterface

extend SMTInterface;

import Binder;
import logic::Integer;
import integer::AST;

import List;
import String;
 
SMTInterface getIntTheorySMTInterface() = <constructSMTVars, <compileVariableDeclaration, compile>, <getValues, mergeModel, negateVariable>>;

set[SMTVar] constructSMTVars(Environment env) = {<"<name>_int", integers()> | str relName <- env, Binding b := env[relName], Index idx <- b, idx.theory == integers(), intVar(str name) := b[idx]};

str compileVariableDeclaration(SMTVar var) = "(declare-const <var.name> Int)" when var.theory == integers();
default str compileVariableDeclaration(SMTVar var) = "";

str compile(\int(int i), str (Formula) _)                                       = "<i>";
str compile(intVar(str name), str (Formula) _)                                  = "<name>_int";
str compile(lt(Formula lhs, Formula rhs), str (Formula) compileAll)             = "(\< <compileAll(lhs)> <compileAll(rhs)>)";
str compile(lte(Formula lhs, Formula rhs), str (Formula) compileAll)            = "(\<= <compileAll(lhs)> <compileAll(rhs)>)";
str compile(gt(Formula lhs, Formula rhs), str (Formula) compileAll)             = "(\> <compileAll(lhs)> <compileAll(rhs)>)";
str compile(gte(Formula lhs, Formula rhs), str (Formula) compileAll)            = "(\>= <compileAll(lhs)> <compileAll(rhs)>)";
str compile(equal(Formula lhs, Formula rhs), str (Formula) compileAll)          = "(= <compileAll(lhs)> <compileAll(rhs)>)";
str compile(addition(Formula lhs, Formula rhs), str (Formula) compileAll)       = "(+ <compileAll(lhs)> <compileAll(rhs)>)";
str compile(substraction(Formula lhs, Formula rhs), str (Formula) compileAll)   = "(- <compileAll(lhs)> <compileAll(rhs)>)";
str compile(multiplication(Formula lhs, Formula rhs), str (Formula) compileAll) = "(* <compileAll(lhs)> <compileAll(rhs)>)";
str compile(division(Formula lhs, Formula rhs), str (Formula) compileAll)       = "(/ <compileAll(lhs)> <compileAll(rhs)>)";

default str compile(integer::AST::Formula _, str (Formula) _) = "";

Model getValues(map[str, str] smtValues, set[SMTVar] smtVars) =
  (var : toFormula(smtValues[var.name]) | SMTVar var <- smtVars, var.name in smtValues, var.theory == integers());
 
Formula toFormula(str someVal) {
  try {
    return \int(toInt(someVal));
  } catch ex: {
    throw "Unable to construct Integer formula with value \'<someVal>\'";
  }
}

Environment mergeModel(Model foundValues, Environment env) {
  return visit(env) {
    case intVar(str name) => foundValues[<"<name>_int", integers()>] when <"<name>_int", integers()> in foundValues
  }
}

//str negateVariable(SMTVar var, Model model) = "(not (= <var.name> <i>))" when var.theory == integers(), \int(int i) := model[var];
default str negateVariable(SMTVar _, Model _) = "";