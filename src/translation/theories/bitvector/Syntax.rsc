module translation::theories::bitvector::Syntax

extend translation::Syntax;

syntax Domain = bv: "bv" "(" Int bits ")";

syntax Literal 
  = bvIntLit : "[bv]" IntLit lit 
  | bvHexLit : "#x" HexLit lit
  ;

syntax AlleFormula
  = bvlt:       "[bv]" AlleExpr lhs "\<"  AlleExpr rhs
  | bvlte:      "[bv]" AlleExpr lhs "\<=" AlleExpr rhs
  | bvgt:       "[bv]" AlleExpr lhs "\>"  AlleExpr rhs
  | bvgte:      "[bv]" AlleExpr lhs "\>=" AlleExpr rhs
  | bvlt:       "[bvu]" AlleExpr lhs "\<"  AlleExpr rhs
  | bvlte:      "[bvu]" AlleExpr lhs "\<=" AlleExpr rhs
  | bvgt:       "[bvu]" AlleExpr lhs "\>"  AlleExpr rhs
  | bvgte:      "[bvu]" AlleExpr lhs "\>=" AlleExpr rhs
  | bvEqual:    "[bv]" AlleExpr lhs "="   AlleExpr rhs
  | bvInequal:  "[bv]" AlleExpr lhs "!="  AlleExpr rhs
  ;
  
syntax AlleExpr
  = variable:             Variable v
  > bvIntLit:             "[bv]" IntLit lit 
  | bvHexLit:             "#x" HexLit lit
  > attributeLookup:      AlleExpr expr "::" AttributeName name
  > bvNeg:                "[bv]" "-" AlleExpr e
  > left bvMult:          "[bv]" AlleExpr lhs "*" AlleExpr rhs
  | bvUnRem:              "[bvu]" AlleExpr lhs "/" AlleExpr rhs
  | bvRem:                "[bv]" AlleExpr lhs "/" AlleExpr rhs
  | bvMod:                "[bv]" AlleExpr lhs "%" AlleExpr rhs
  > left bvAdd:           "[bv]" AlleExpr lhs "+" AlleExpr rhs 
  | left bvSub:           "[bv]" AlleExpr lhs "-" AlleExpr rhs
  > bvShiftLeft:          "[bv]" AlleExpr lhs "\<\<" AlleExpr rhs
  | bvUnShiftRight:       "[bvu]" AlleExpr lhs "\>\>" AlleExpr rhs
  | bvShiftRight:         "[bv]" AlleExpr lhs "\>\>" AlleExpr rhs
  | bvOr:                 "[bv]" AlleExpr lhs "|" AlleExpr rhs
  | bvAnd:                "[bv]" AlleExpr lhs "&" AlleExpr rhs
  | bvXor:                "[bv]" AlleExpr lhs "^" AlleExpr rhs
  | bvNot:                "[bv]" "~" AlleExpr e
  | bvNand:               "[bv]" AlleExpr lhs "~&" AlleExpr rhs
  | bvNor:                "[bv]" AlleExpr lhs "~|" AlleExpr rhs
  | bvXnor:               "[bv]" AlleExpr lhs "~^" AlleExpr rhs 
  ; 

lexical IntLit = [0-9]+;
lexical HexLit = [0-9abcdef]+;

keyword Keywords = "[bvu]" | "[bv]" | "#x";