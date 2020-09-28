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

lexical Val = [\-a-z A-Z_.0-9!#\\@] !<< [\-a-z A-Z_.0-9!#\\@]+ !>> [\-a-z A-Z_.0-9!#\\@];

//lexical StringCharacter
//  = "\\" [\" \' \< \> \\ b f n r t] 
//  | UnicodeEscape 
//  | ![\" \' \< \> \\]
//  | [\n][\ \t \u00A0 \u1680 \u2000-\u200A \u202F \u205F \u3000]* [\'] // margin 
//  ;
//
//lexical UnicodeEscape
//  = utf16: "\\" [u] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] 
//  | utf32: "\\" [U] (("0" [0-9 A-F a-f]) | "10") [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] // 24 bits 
//  | ascii: "\\" [a] [0-7] [0-9A-Fa-f]
//  ;
