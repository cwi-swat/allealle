module theories::relational::AST

extend theories::AST;

data Theory = relTheory();
  
data AlleFormula
  = empty(Expr expr)
  | atMostOne(Expr expr)
  | exactlyOne(Expr expr)
  | nonEmpty(Expr expr)
  | subset(Expr lhsExpr, Expr rhsExpr)
  | equal(Expr lhsExpr, Expr rhsExpr)
  | inequal(Expr lhsExpr, Expr rhsExpr)
  | negation(AlleFormula form)
  | conjunction(AlleFormula lhsForm, AlleFormula rhsForm)
  | disjunction(AlleFormula lhsForm, AlleFormula rhsForm)
  | implication(AlleFormula lhsForm, AlleFormula rhsForm)
  | equality(AlleFormula lhsForm, AlleFormula rhsForm)
  | universal(list[VarDeclaration] decls, AlleFormula form)
  | existential(list[VarDeclaration] decls, AlleFormula form) 
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
  | ifThenElse(AlleFormula caseForm, Expr thenExpr, Expr elseExpr)
  | comprehension(list[VarDeclaration] decls, AlleFormula form)
  ;

data VarDeclaration = varDecl(str name, Expr binding);