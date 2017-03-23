module theories::integer::SMTInterface

extend theories::SMTInterface;

import theories::Binder;
import logic::Integer;
import theories::integer::AST;

import List;
import String;
 
Maybe[str] constructExtendedTheoryVar(intVar(str name)) = just("<name>_int");
Maybe[str] constructExtendedTheoryVar(\int(int _)) = nothing();

str compileVariableDeclaration(SMTVar var) = "(declare-const <var.name> Int)" when var.theory == intTheory();

str compile(\int(int i))                              = "<i>";
str compile(intVar(str name))                         = "<name>_int";
str compile(neg(Formula f))                           = "(- <compile(f)>)";
str compile(lt(Formula lhs, Formula rhs))             = "(\< <compile(lhs)> <compile(rhs)>)";
str compile(lte(Formula lhs, Formula rhs))            = "(\<= <compile(lhs)> <compile(rhs)>)";
str compile(gt(Formula lhs, Formula rhs))             = "(\> <compile(lhs)> <compile(rhs)>)";
str compile(gte(Formula lhs, Formula rhs))            = "(\>= <compile(lhs)> <compile(rhs)>)";
str compile(equal(Formula lhs, Formula rhs))          = "(= <compile(lhs)> <compile(rhs)>)";
str compile(addition(list[Formula] forms))             = "(+ <for (f <- forms) {><compile(f)> <}>)";
str compile(multiplication(list[Formula] forms))       = "(* <for (f <- forms) {><compile(f)> <}>)"; 
str compile(division(Formula lhs, Formula rhs))       = "(/ <compile(lhs)> <compile(rhs)>)";

Formula getValue(str smtValue, SMTVar var) = toFormula(smtValue) when var.theory == intTheory();
 
Formula toFormula(str someVal) {
  try {
    return \int(toInt(someVal));
  } catch ex: {
    throw "Unable to construct Integer formula with value \'<someVal>\'";
  }
}

Formula mergeModel(Model foundValues, intVar(str name)) = foundValues[<"<name>_int", intTheory()>] when <"<name>_int", intTheory()> in foundValues;
Formula mergeModel(Model foundValues, \int(int i)) = \int(i);

str negateVariable(SMTVar var, \int(int i)) = "";