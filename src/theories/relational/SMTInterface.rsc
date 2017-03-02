module theories::relational::SMTInterface

extend theories::SMTInterface;

import logic::Propositional;
import theories::relational::AST;

import List;
 
Maybe[SMTVar] constructSMTVar(var(str name)) = just(<name, relTheory()>);

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
