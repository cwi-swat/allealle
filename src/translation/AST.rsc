module translation::AST

data Problem = problem(list[RelationDef] relations, list[AlleFormula] constraints);

data RelationDef
  = relation(str name, list[HeaderAttribute] heading, RelationalBound bounds)
  ;

data HeaderAttribute
  = header(str name, Domain dom)
  ;

data RelationalBound
  = exact(list[AlleTuple] tuples)
  | atMost(list[AlleTuple] upper)
  | atLeastAtMost(list[AlleTuple] lower, list[AlleTuple] upper)
  ;

data AlleTuple 
  = tup(list[AlleValue] values)
  | range(list[RangedValue] from, list[RangedValue] to)
  ;  

data AlleValue
  = idd(Id id)
  | alleLit(AlleLiteral lit)
  | hole()
  ;

data RangedValue
  = id(str prefix, int numm)
  | idOnly(Id id)
  | templateLit(AlleLiteral lit)
  | templateHole()
  ;

alias Id = str;

data Domain 
  = id()
  ;
    
data AlleLiteral
  = idLit(Id id)
  ; 

data AlleFormula(loc origLoc = |unknown://|)
  = \filter(AlleExpr expr, Criteria criteria)
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
  | let(list[VarBinding] bindings, AlleFormula form)
  | universal(list[VarDeclaration] decls, AlleFormula form)
  | existential(list[VarDeclaration] decls, AlleFormula form) 
  ; 
 
data AlleExpr
  = relvar(str name)
  | rename(AlleExpr expr, list[Rename] renames)
  | project(AlleExpr expr, list[str] attributes)
  | select(AlleExpr expr, Criteria criteria)
  | union(AlleExpr lhs, AlleExpr rhs)
  | intersection(AlleExpr lhs, AlleExpr rhs)
  | difference(AlleExpr lhs, AlleExpr rhs)
  | product(AlleExpr lhs, AlleExpr rhs)
  | naturalJoin(AlleExpr lhs, AlleExpr rhs)
  | transpose(TupleAttributeSelection tas, AlleExpr expr)
  | closure(TupleAttributeSelection tas, AlleExpr r)
  | reflexClosure(TupleAttributeSelection tas, AlleExpr r)
  ;

data VarDeclaration = varDecl(str name, AlleExpr binding);

data VarBinding = varBinding(str name, AlleExpr binding);

data TupleAttributeSelection 
  = order(str first, str second)
  ;

data Rename 
  = rename(str new, str orig)
  ;

data Criteria
  = equal(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)
  | inequal(CriteriaExpr lhsExpr, CriteriaExpr rhsExpr)
  | and(Criteria lhs, Criteria rhs)
  | or(Criteria lhs, Criteria rhs)
  | not(Criteria crit)
  ;


data CriteriaExpr
  = att(str name) 
  | litt(AlleLiteral l)
  ;
