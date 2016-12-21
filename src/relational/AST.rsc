module relational::AST

extend AST;

data Theory = relational();
  
data Formula
  = empty(Expr expr)
  | atMostOne(Expr expr)
  | exactlyOne(Expr expr)
  | nonEmpty(Expr expr)
  | subset(Expr lhsExpr, Expr rhsExpr)
  | equal(Expr lhsExpr, Expr rhsExpr)
  | negation(Formula form)
  | conjunction(Formula lhsForm, Formula rhsForm)
  | disjunction(Formula lhsForm, Formula rhsForm)
  | implication(Formula lhsForm, Formula rhsForm)
  | equality(Formula lhsForm, Formula rhsForm)
  | universal(list[VarDeclaration] decls, Formula form)
  | existential(list[VarDeclaration] decls, Formula form) 
  ; 

data Expr
  = variable(str name)
  | transpose(Expr expr)
  | closure(Expr expr)
  | reflexClosure(Expr expr)
  | union(Expr lhs, Expr rhs) 
  | intersection(Expr lhs, Expr rhs)
  | difference(Expr lhs, Expr rhs)
  | \join(Expr lhs, Expr rhs)
  | accessorJoin(Expr col, Expr select)
  | product(Expr lhs, Expr rhs)
  | ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr)
  | comprehension(list[VarDeclaration] decls, Formula form)
  ;

data VarDeclaration = varDecl(str name, Expr binding);