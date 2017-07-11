module theories::integer::SMTInterface

extend theories::SMTInterface;

import theories::Binder;
import logic::Integer;
import theories::integer::AST;
import theories::integer::Translator;

import List;
import String; 
 
Maybe[tuple[str,Theory]] constructExtendedTheoryVar({form(Formula _, equal(intVar(str name), Formula r))}) = just(<"<name>", intTheory()>); 
//Maybe[tuple[str,Theory]] constructExtendedTheoryVar({form(Formula _, equal(Formula _, \int(int _)))}) = nothing();

Maybe[tuple[str,Theory]] constructExtendedTheoryVar(atomAndTheory(str atom, intTheory())) = just(<"<atom>", intTheory()>); 
Maybe[tuple[str,Theory]] constructExtendedTheoryVar(atomTheoryAndValue(str atom, intTheory(), intExpr(Expr expr))) = just(<"<atom>", intTheory()>) when \int(int i) := exprToForm(expr); 
default Maybe[tuple[str,Theory]] constructExtendedTheoryVar(atomTheoryAndValue(str atom, intTheory(), intExpr(Expr expr))) = just(<atom, intTheory()>); 

str compileVariableDeclaration(SMTVar var) = "(declare-const <var.name> Int)" when var.theory == intTheory();

str compileAtomValueExpr(atomTheoryAndValue(str atom, intTheory(), intExpr(Expr expr))) = "(= <atom> <compile(f)>)" 
  when Formula f := exprToForm(expr); 

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

Formula getValue(Value smtValue, SMTVar var) = toFormula(smtValue) when var.theory == intTheory();
 
Formula toFormula((Value)`<Val v>`) = \int(toInt("<v>")); 
Formula toFormula((Value)`(- <Val v>)`) = \int(-toInt("<v>")); 
default Formula toFormula(Value v) { throw "Unable to convert found value <v> to an Integer formula"; } 

AtomValue findAtomValue(Atom a, intTheory(), SMTModel smtModel) = intExpr(intLit(val)) when <a, intTheory()> in smtModel, \int(int val) := smtModel[<a, intTheory()>];
 
str negateAtomVariable(varAtom(Atom a, intTheory(), intExpr(intLit(int i)))) = "(not (= <a> <i>))";