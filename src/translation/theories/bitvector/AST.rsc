module translation::theories::bitvector::AST

data Literal 
  = bvIntLit(int lit) 
  | bvHexLit(str lit)
  ;

data AlleFormula
  = bvlt(AlleExpr lhs, AlleExpr rhs)
  | bvlte(AlleExpr lhs, AlleExpr rhs)
  | bvgt(AlleExpr lhs, AlleExpr rhs)
  | bvgte(AlleExpr lhs, AlleExpr rhs)
  | bvlt(AlleExpr lhs, AlleExpr rhs)
  | bvlte(AlleExpr lhs, AlleExpr rhs)
  | bvgt(AlleExpr lhs, AlleExpr rhs)
  | bvgte(AlleExpr lhs, AlleExpr rhs)
  | bvEqual(AlleExpr lhs, AlleExpr rhs)
  | bvInequal(AlleExpr lhs, AlleExpr rhs)
  ;
  
data AlleExpr
  = variable(str var)
  | bvIntLit(int lit) 
  | bvHexLit(str lit)
  | bvNeg:                "[bv]" "-" AlleExpr e
  | left bvMult:          "[bv]" AlleExpr lhs "*" AlleExpr rhs
  | bvUnRem:              "[bvu]" AlleExpr lhs "/" AlleExpr rhs
  | bvRem:                "[bv]" AlleExpr lhs "/" AlleExpr rhs
  | bvMod:                "[bv]" AlleExpr lhs "%" AlleExpr rhs
  | left bvAdd:           "[bv]" AlleExpr lhs "+" AlleExpr rhs 
  | left bvSub:           "[bv]" AlleExpr lhs "-" AlleExpr rhs
  | bvShiftLeft:          "[bv]" AlleExpr lhs "\<\<" AlleExpr rhs
  | bvUnShiftRight:       "[bvu]" AlleExpr lhs "\>\>" AlleExpr rhs
  | bvShiftRight:         "[bv]" AlleExpr lhs "\>\>" AlleExpr rhs
  | bvOr:                 "[bv]" AlleExpr lhs "|" AlleExpr rhs
  | bvAnd:                "[bv]" AlleExpr lhs "&" AlleExpr rhs
  | bvNot:                "[bv]" "!" AlleExpr e
  | bvNand:               "[bv]" AlleExpr lhs "!&" AlleExpr rhs
  | bvNor:                "[bv]" AlleExpr lhs "!|" AlleExpr rhs
  | bvXnor:               "[bv]" AlleExpr lhs "x!|" AlleExpr rhs 
  ;