module translation::SMTValueSyntax

extend translation::Layout;

start syntax SmtValues = "(" VarAndValue+ values")";

syntax VarAndValue = "(" VarName name SmtValue val ")"; 
  
syntax SmtValue
  = Val
  | "\"" Val "\""
  | "\"" "\""
  | Val Val 
  | "(" SmtValue ")"
  ;   
  
lexical VarName = [A-Za-z_.0-9!+\-] !<< [A-Za-z_.0-9!+\-]+ !>> [A-Za-z_.0-9!+\-];

lexical Val = [\-a-z A-Z_.0-9!#] !<< [\-a-z A-Z_.0-9!#]+ !>> [\-a-z A-Z_.0-9!#];