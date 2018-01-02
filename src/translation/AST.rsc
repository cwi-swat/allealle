module translation::AST

data Problem = problem(list[RelationDef] relations, list[AlleFormula] constraints);

data RelationDef
  = relation(str name, list[HeaderAttribute] headers, RelationalBound bounds)
  ;

data HeaderAttribute
  = header(str name, Domain dom)
  | idHeader(Domain dom)
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

data Domain 
  = id()
  | \fail()
  ;
    
data Literal = none(); 

data AlleFormula(loc origLoc = |unknown://|)
  = \filter(AlleExpr expr, Restriction restriction)
  | empty(AlleExpr expr)
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
  = relvar(str name)
  | lit(Literal l)
  | rename(AlleExpr expr, list[Rename] renames)
  | projection(AlleExpr expr, list[str] attributes)
  | restriction(AlleExpr expr, Restriction restriction)
  | transpose(TupleAttributeSelection tas, AlleExpr expr)
  | transpose(AlleExpr expr)
  | closure(TupleAttributeSelection tas, AlleExpr r)
  | closure(AlleExpr r)
  | reflexClosure(TupleAttributeSelection tas, AlleExpr r)
  | reflexClosure(AlleExpr r)
  | naturalJoin(AlleExpr lhs, AlleExpr rhs)
  | dotJoin(AlleExpr lhs, AlleExpr rhs)
  | union(AlleExpr lhs, AlleExpr rhs)
  | intersection(AlleExpr lhs, AlleExpr rhs)
  | difference(AlleExpr lhs, AlleExpr rhs)
  | product(AlleExpr lhs, AlleExpr rhs)
  ;

data VarDeclaration = varDecl(str name, AlleExpr binding);

data TupleAttributeSelection 
  = order(str first, str second)
  ;

data Rename 
  = rename(str new, str orig)
  ;

data Restriction
  = equal(RestrictionExpr lhsExpr, RestrictionExpr rhsExpr)
  | and(Restriction lhs, Restriction rhs)
  | or(Restriction lhs, Restriction rhs)
  | not(Restriction)
  ;


data RestrictionExpr
  = att(str name)
  | lit(Literal l)
  ;
