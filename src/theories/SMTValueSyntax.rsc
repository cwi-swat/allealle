module theories::SMTValueSyntax

extend lang::std::Layout;

start syntax Values = "(" VarAndValue+ values")";

syntax VarAndValue = "(" VarName name Value val ")"; 
  
syntax Value 
  = Val
  | Val Val
  | "(" Value ")"
  ;
  
lexical VarName = [A-Za-z_.0-9] !<< [A-Za-z_.0-9]+ !>> [A-Za-z_.0-9];

lexical Val = [\-a-z A-Z_.0-9#] !<< [\-a-z A-Z_.0-9#]+ !>> [\-a-z A-Z_.0-9#];