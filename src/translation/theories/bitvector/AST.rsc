module translation::theories::bitvector::AST

data Domain
  = bv(int bits)
  ;

data Literal 
  = bvIntLit(int lit) 
  | bvHexLit(str lit)
  | bvBinLit(int lit)
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
  | bvNeg(AlleExpr e)
  | bvMult(AlleExpr lhs, AlleExpr rhs)
  | bvUnRem(AlleExpr lhs, AlleExpr rhs)
  | bvRem(AlleExpr lhs, AlleExpr rhs)
  | bvMod(AlleExpr lhs, AlleExpr rhs)
  | bvAdd(AlleExpr lhs, AlleExpr rhs)
  | bvSub(AlleExpr lhs, AlleExpr rhs)
  | bvShiftLeft(AlleExpr lhs, AlleExpr rhs)
  | bvUnShiftRight( AlleExpr lhs, AlleExpr rhs)
  | bvShiftRight(AlleExpr lhs, AlleExpr rhs)
  | bvOr(AlleExpr lhs, AlleExpr rhs)
  | bvAnd(AlleExpr lhs, AlleExpr rhs)
  | bvNot(AlleExpr e)
  | bvNand(AlleExpr lhs, AlleExpr rhs)
  | bvNor(AlleExpr lhs, AlleExpr rhs)
  | bvXnor(AlleExpr lhs, AlleExpr rhs) 
  ;