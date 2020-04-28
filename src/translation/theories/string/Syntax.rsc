module translation::theories::string::Syntax

syntax Domain = "str";

syntax Literal 
  = strLit: StrLit s
  ; 

syntax CriteriaExpr
  = length:            "length" "(" CriteriaExpr expr ")"
  | toInt:             "toInt" "(" CriteriaExpr expr ")"
  | toStr:             "toStr" "(" CriteriaExpr expr ")"
  > left concat:       CriteriaExpr lhs "++" CriteriaExpr rhs
  ;

lexical StrLit = @category="Constant"  "\"" StringCharacter* "\""; 

lexical StringCharacter
  = "\\" [\" \' \< \> \\ b f n r t] 
  | UnicodeEscape 
  | ![\" \' \< \> \\]
  | [\n][\ \t \u00A0 \u1680 \u2000-\u200A \u202F \u205F \u3000]* [\'] // margin 
  ;

lexical UnicodeEscape
  = utf16: "\\" [u] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] 
  | utf32: "\\" [U] (("0" [0-9 A-F a-f]) | "10") [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] // 24 bits 
  | ascii: "\\" [a] [0-7] [0-9A-Fa-f]
  ;

keyword Keywords = "str";