module theories::PreProcessor

import theories::AST;

Problem replaceConstants(Problem problem) {
  bool exists(str atomName) = true when AtomDecl ad <- problem.uni.atoms, ad.atom == atomName;
  default bool exists(str atomName) = false;
  
  list[AtomDecl] constantAtoms = [];
  list[RelationalBound] constantRelations = [];
  
  void addRelation(str constantName, AtomDecl ad) { 
    println(ad);
    constantAtoms += [ad];
    constantRelations += [relationalBound(constantName, 1, [\tuple([ad.atom])], [\tuple([ad.atom])])];
  }
  
  
  problem = visit(problem) {
    case Expr expr => replaceConstants(expr, addRelation, exists) when isConstant(expr)
  }
  
  problem.uni.atoms += constantAtoms;
  problem.bounds += constantRelations;
  
  return problem;
}

default bool isConstant(Expr _) = false;
default Expr replaceConstants(Expr orig, void (str, AtomDecl) update, bool (str) exists) { throw "No constant replacing function defined for constant expression \'<orig>\'"; } 