module translation::Unparser

import translation::AST;
import List;


str unparse(problem(list[Relation] relations, list[AlleFormula] constraints)) = 
  "<for (Relation r <- relations) {><unparse(r)>
  '<}>
  '
  '<for(AlleFormula f <- constraints) {><unparse(f)>
  '<}>
  '";

str unparse(relation(str name, int arityOfIds, RelationalBound bounds)) =
  "<name> (<arityOfIds>) <unparse(bounds)>";

str unparse(relationWithAttributes(str name, int arityOfIds, list[AttributeHeader] headers, RelationalBound bounds)) =
  "<name> (<arityOfIds> :: <intercalate(",", [unparse(h) | AttributeHeader h <- headers])>) <unparse(bounds)>";

str unparse(header(str name, Domain dom)) =
  "<name> : <unparse(dom)>";

str unparse(exact(list[Tuple] tuples)) =
  "= {<intercalate(",", [unparse(t) | Tuple t <- tuples])>}";

str unparse(atMost(list[Tuple] upper)) =
  "\<= {<intercalate(",", [unparse(t) | Tuple t <- upper])>}";

str unparse(atLeastAtMost(list[Tuple] lower, list[Tuple] upper)) = 
  "\>= {<intercalate(",", [unparse(t) | Tuple t <- lower])>} \<= {<intercalate(",", [unparse(t) | Tuple t <- upper])>}";
 
str unparse(tup(list[Value] values)) =
  "\<<intercalate(",", [unparse(v) | Value v <- values])>\>";

str unparse(id(Id id)) = id;
str unparse(lit(Literal lit)) = unparse(lit);
str unparse(hole()) = "?";

default str unparse(Literal l) { throw "No uparse function for literal \'<l>\'"; }
  
str unparse(id()) = "";
default str unparse(Domain d) { throw "No unparse function for domain \'<d>\'"; }

str unparse(empty(AlleExpr expr))                                                   = "(no <unparse(expr)>)";
str unparse(atMostOne(AlleExpr expr))                                               = "(lone <unparse(expr)>)";
str unparse(exactlyOne(AlleExpr expr))                                              = "(one <unparse(expr)>)";
str unparse(nonEmpty(AlleExpr expr))                                                = "(some <unparse(expr)>)"; 
str unparse(subset(AlleExpr lhsExpr, AlleExpr rhsExpr))                             = "(<unparse(lhsExpr)> in <unparse(rhsExpr)>)";
str unparse(equal(AlleExpr lhsExpr, AlleExpr rhsExpr))                              = "(<unparse(lhsExpr)> == <unparse(rhsExpr)>)";
str unparse(inequal(AlleExpr lhsExpr, AlleExpr rhsExpr))                            = "(<unparse(lhsExpr)> !== <unparse(rhsExpr)>)";
str unparse(negation(AlleFormula form))                                             = "(not <unparse(form)>)";
str unparse(conjunction(AlleFormula lhsForm, AlleFormula rhsForm))                  = "(<unparse(lhsForm)> && <unparse(rhsForm)>)";
str unparse(disjunction(AlleFormula lhsForm, AlleFormula rhsForm))                  = "(<unparse(lhsForm)> || <unparse(rhsForm)>)";
str unparse(implication(AlleFormula lhsForm, AlleFormula rhsForm))                  = "(<unparse(lhsForm)> =\> <unparse(rhsForm)>)";
str unparse(equality(AlleFormula lhsForm, AlleFormula rhsForm))                     = "(<unparse(lhsForm)> \<=\> <unparse(rhsForm)>)";  
str unparse(universal(list[VarDeclaration] decls, AlleFormula form))                = "(forall <intercalate(", ", [unparse(d) | VarDeclaration d <- decls])> | <unparse(form)>)";
str unparse(existential(list[VarDeclaration] decls, AlleFormula form))              = "(exists <intercalate(", ", [unparse(d) | VarDeclaration d <- decls])> | <unparse(form)>)";
str unparse(let(list[VarDeclaration] decls, AlleFormula form))                      = "(let <intercalate(", ", [unparse(d) | VarDeclaration d <- decls])> | <unparse(form)>)";
default str unparse(AlleFormula f) { throw "No unparse function for formula \'<f>\'"; }

str unparse(variable(str name))                                                     = name;
str unparse(attributeLookup(AlleExpr expr, str name))                               = "<unparse(expr)>::<name>";
str unparse(transpose(AlleExpr expr))                                               = "(~<unparse(expr)>)";
str unparse(closure(AlleExpr expr))                                                 = "(^<unparse(expr)>)";
str unparse(reflexClosure(AlleExpr expr))                                           = "(*<unparse(expr)>)";
str unparse(union(AlleExpr lhs, AlleExpr rhs))                                      = "(<unparse(lhs)>++<unparse(rhs)>)";
str unparse(override(AlleExpr lhs, AlleExpr rhs))                                   = "(<unparse(lhs)>+++<unparse(rhs)>)";
str unparse(intersection(AlleExpr lhs, AlleExpr rhs))                               = "(<unparse(lhs)>&<unparse(rhs)>)";
str unparse(difference(AlleExpr lhs, AlleExpr rhs))                                 = "(<unparse(lhs)>\\<unparse(rhs)>)";
str unparse(\join(AlleExpr lhs, AlleExpr rhs))                                      = "(<unparse(lhs)>.<unparse(rhs)>)";
str unparse(accessorJoin(AlleExpr col, AlleExpr select))                            = "(<unparse(col)>[<unparse(select)>])";
str unparse(product(AlleExpr lhs, AlleExpr rhs))                                    = "(<unparse(lhs)>-\><unparse(rhs)>)";
str unparse(ifThenElse(AlleFormula caseForm, AlleExpr thenExpr, AlleExpr elseExpr)) = "(<unparse(caseForm)> ? <unparse(thenExpr)> : <unparse(elseExpr)>)";
str unparse(comprehension(list[VarDeclaration] decls, AlleFormula form))            = "{<intercalate(", ", [unparse(d) | VarDeclaration d <- decls])> | <unparse(form)>}";
default str unparse(AlleExpr exp) { throw "No unparser implemented for \'<exp>\'"; }

str unparse(varDecl(str name, AlleExpr binding)) = "<name>:<unparse(binding)>";
