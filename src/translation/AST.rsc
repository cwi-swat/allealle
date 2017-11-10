module translation::AST

data Problem = problem(list[Relation] relations, list[AlleFormula] constraints);

data Relation 
  = relation(str name, int arityOfIds, RelationalBound bounds)
  | relationWithAttributes(str name, int arityOfIds, list[AttributeHeader] headers, RelationalBound bounds)
  ;

data AttributeHeader
  = header(str name, Domain dom)
  ;

data RelationalBound
  = exact(list[Tuple] tuples)
  | atMost(list[Tuple] upper)
  | atLeastAtMost(list[Tuple] lower, list[Tuple] upper)
  ;

data Tuple 
  = tup(list[Value] values)
  | range(list[RangedValue] from, list[RangedValue] to)
  ;  

data Value
  = id(Id id)
  | lit(Literal lit)
  | hole()
  ;

data RangedValue
  = id(str prefix, int numm)
  | idOnly(Id id)
  | templateLit(Literal lit)
  | templateHole()
  ;

alias Id = str;

data Domain = id();  
data Literal = none(); 

data AlleFormula
  = empty(AlleExpr expr)
  | atMostOne(AlleExpr expr)
  | exactlyOne(AlleExpr expr)
  | nonEmpty(AlleExpr expr)
  | subset(AlleExpr lhsExpr, AlleExpr rhsExpr)
  | equal(AlleExpr lhsExpr, AlleExpr rhsExpr)
  | inequal(AlleExpr lhsExpr, AlleExpr rhsExpr)
  | negation(AlleFormula form)
  | conjunction(AlleFormula lhsForm, AlleFormula rhsForm)
  | disjunction(AlleFormula lhsForm, AlleFormula rhsForm)
  | implication(AlleFormula lhsForm, AlleFormula rhsForm)
  | equality(AlleFormula lhsForm, AlleFormula rhsForm)
  | let(list[VarDeclaration] decls, AlleFormula form)
  | universal(list[VarDeclaration] decls, AlleFormula form)
  | existential(list[VarDeclaration] decls, AlleFormula form) 
  ; 
 
data AlleExpr
  = variable(str name)
  | attributeLookup(AlleExpr expr, str name)
  | transpose(AlleExpr expr)
  | closure(AlleExpr expr)
  | reflexClosure(AlleExpr expr)
  | union(AlleExpr lhs, AlleExpr rhs) 
  | override(AlleExpr lhs, AlleExpr rhs)
  | intersection(AlleExpr lhs, AlleExpr rhs)
  | difference(AlleExpr lhs, AlleExpr rhs)
  | \join(AlleExpr lhs, AlleExpr rhs)
  | accessorJoin(AlleExpr col, AlleExpr select)
  | product(AlleExpr lhs, AlleExpr rhs)
  | ifThenElse(AlleFormula caseForm, AlleExpr thenExpr, AlleExpr elseExpr)
  | comprehension(list[VarDeclaration] decls, AlleFormula form)
  ;

data VarDeclaration = varDecl(str name, AlleExpr binding);
