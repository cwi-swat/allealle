module theories::integer::SMTInterface

extend theories::SMTInterface;

import theories::Binder;
import logic::Integer;
import theories::integer::AST;
import theories::integer::Translator;

import List;
import String; 

tuple[str, Theory] constructAtomVar(Atom a, Attribute at) = <"<a>!<at.name>", intTheory()> when at.theory == intTheory();
tuple[str, Theory] constructAttributeVar(<Formula _, equal(intVar(str name), Formula _)>) = <name, intTheory()>;

str compileVariableDeclaration(SMTVar var) = "(declare-const <var.name> Int)" when var.theory == intTheory();

str compileAttributeValue(Atom a, attributeAndValue(str name, intTheory(), intExpr(Expr expr))) = "(= <a>!<name> <compile(exprToForm(expr))>)"; 

str compile(\int(int i))                          = "<i>"; 
str compile(intVar(str name))                     = "<name>";
str compile(neg(Formula f))                       = "(- <compile(f)>)"; 
str compile(lt(Formula lhs, Formula rhs))         = "(\< <compile(lhs)> <compile(rhs)>)";
str compile(lte(Formula lhs, Formula rhs))        = "(\<= <compile(lhs)> <compile(rhs)>)";
str compile(gt(Formula lhs, Formula rhs))         = "(\> <compile(lhs)> <compile(rhs)>)";
str compile(gte(Formula lhs, Formula rhs))        = "(\>= <compile(lhs)> <compile(rhs)>)";
str compile(equal(Formula lhs, Formula rhs))      = "(= <compile(lhs)> <compile(rhs)>)";
str compile(inequal(Formula lhs, Formula rhs))    = "(not (= <compile(lhs)> <compile(rhs)>))";
str compile(addition(list[Formula] forms))        = "(+ <for (f <- forms) {><compile(f)> <}>)";
str compile(multiplication(list[Formula] forms))  = "(* <for (f <- forms) {><compile(f)> <}>)";
str compile(modulo(Formula lhs, Formula rhs))     = "(mod <compile(lhs)> <compile(rhs)>)";  
str compile(division(Formula lhs, Formula rhs))   = "(div <compile(lhs)> <compile(rhs)>)"; 

Formula getValue(SmtValue smtValue, SMTVar var) = toFormula(smtValue) when var.theory == intTheory();
 
Formula toFormula((SmtValue)`<Val v>`) = \int(toInt("<v>")); 
Formula toFormula((SmtValue)`(- <Val v>)`) = \int(-toInt("<v>")); 

Value findAttributeValue(Atom a, str name, intTheory(), SMTModel smtModel) = intExpr(intLit(val)) when <"<a>!<name>", intTheory()> in smtModel, \int(int val) := smtModel[<"<a>!<name>", intTheory()>];
 
str negateAttribute(Atom a, varAttribute(str name, intTheory(), intExpr(intLit(int i)))) = "(not (= <a>!<name> <i>))";