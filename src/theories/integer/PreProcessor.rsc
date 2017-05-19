module theories::integer::PreProcessor

extend theories::PreProcessor;

import theories::integer::AST;

bool isConstant(intLit(_)) = true;

Expr replaceConstants(intLit(int i), void (str, AtomDecl) update, bool (str) exists) {
  if (!exists("c<i>")) {
    AtomDecl consAtom = atomTheoryAndValue("c<i>", intTheory(), intVal(i)); 
    update("C<i>", consAtom);  
  }
  
  return variable("C<i>");
} 