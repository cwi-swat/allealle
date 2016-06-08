module extended::SMTCompiler

extend orig::SMTCompiler;

import logic::Integer;

str compileDeclaredBoolVariables(set[str] vars) = "<("" | "<it>\n(declare-const <v> Bool)" | v <- vars)>";
str compileDeclaredIntVariables(set[str] vars) = "<("" | "<it>\n(declare-const <v>_int Int)" | v <- vars)>";

str compile(\int(int i)) = "<i>";
str compile(intVar(str name)) = "<name>_int";
str compile(lt(Formula lhs, Formula rhs)) = "(\< <compile(lhs)> <compile(rhs)>)";
str compile(lte(Formula lhs, Formula rhs)) = "(\<= <compile(lhs)> <compile(rhs)>)";
str compile(gt(Formula lhs, Formula rhs)) = "(\> <compile(lhs)> <compile(rhs)>)";
str compile(gte(Formula lhs, Formula rhs)) = "(\>= <compile(lhs)> <compile(rhs)>)";
str compile(equal(Formula lhs, Formula rhs)) = "(= <compile(lhs)> <compile(rhs)>)";
str compile(addition(Formula lhs, Formula rhs)) = "(+ <compile(lhs)> <compile(rhs)>)";
str compile(substraction(Formula lhs, Formula rhs)) = "(- <compile(lhs)> <compile(rhs)>)";
str compile(multiplication(Formula lhs, Formula rhs)) = "(* <compile(lhs)> <compile(rhs)>)";
str compile(division(Formula lhs, Formula rhs)) = "(/ <compile(lhs)> <compile(rhs)>)";

