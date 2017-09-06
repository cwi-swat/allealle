module translation::theories::integer::SMTInterface

extend translation::SMTInterface;

import logic::Integer;
import translation::Binder;
import translation::theories::integer::AST;
import translation::theories::integer::Translator;

import List;
import String; 

Maybe[SMTVar] constructAttributeVar(intVar(str name)) = just(<name, \int()>);
Maybe[SMTVar] constructAttributeVar(\int(int _)) = nothing();

str compileVariableDeclaration(<str name, \int()>) = "(declare-const <name> Int)";

str compile(\int(int i))                          = "<i>"; 
str compile(intVar(str name))                     = "<name>";
str compile(neg(Formula f))                       = "(- <compile(f)>)"; 
str compile(abs(Formula f))                       = "(ite (\>= <compF> 0) <compF> (- <compF>))" when str compF := compile(f); 
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

Formula getValue(SmtValue smtValue, <str _, \int()>) = toFormula(smtValue);
 
Formula toFormula((SmtValue)`<Val v>`) = \int(toInt("<v>")); 
Formula toFormula((SmtValue)`(- <Val v>)`) = neg(\int(toInt("<v>"))); 

Maybe[str] getAttributeVarName(\int(_))          = nothing();
Maybe[str] getAttributeVarName(intVar(str name)) = just(name);

Value toValue(\int(int i))      = lit(posInt(i));
Value toValue(neg(\int(int i))) = lit(negInt(i));

tuple[Domain, Value] getAttributeValue(\int(int i), SMTModel _)          = <\int(), lit(posInt(i))>;
tuple[Domain, Value] getAttributeValue(neg(\int(int i)), SMTModel _)     = <\int(), lit(negInt(i))>;
tuple[Domain, Value] getAttributeValue(intVar(str name), SMTModel model) = <\int(), toValue(model[<name,\int()>])> when <name, \int()> in model;

str negateAttribute(\int(), str varName, lit(posInt(int i))) = "(not (= <varName> <i>))";
str negateAttribute(\int(), str varName, lit(negInt(int i))) = "(not (= <varName> (- <i>)))";