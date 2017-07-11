module theories::Unparser

import theories::AST;
import List;

str unparse(problem(Universe uni, list[RelationalBound] bounds, list[AlleFormula] constraints)) =
  "<unparse(uni)>
  '
  '<for(RelationalBound rb <- bounds) {><unparse(rb)>
  '<}>
  '
  '<for(AlleFormula f <- constraints) {><unparse(f)>
  '<}>
  '";

str unparse(universe(list[AtomDecl] atoms)) =
  "{<intercalate(",",[unparse(ad) | AtomDecl ad <- atoms])>}";

str unparse(atomOnly(Atom atom)) = atom;
str unparse(atomWithAttributes(Atom atom, list[Attribute] attributes)) = "<atom>{<intercalate(", ", [unparse(a) | Attribute a <- attributes])>}";

str unparse(attribute(str name, Theory theory)) = "<name>(<unparse(theory)>)";
str unparse(attributeAndValue(str name, Theory theory, Value val)) = "<name>(<unparse(theory)>)=<unparse(val)>"; 

str unparse(relTheory()) = "";
default str unparse(Theory t) { throw "No unparse function for \'<t>\'"; }

str unparse(none()) = "";

str unparse(relationalBound(str relName, int arity, list[Tuple] lowerBounds, list[Tuple] upperBounds)) =
  "<relName>:<arity> [{<intercalate(",", [unparse(t) | Tuple t <- lowerBounds])>}, {<intercalate(",", [unparse(t) | Tuple t <- upperBounds])>}]";

str unparse(\tuple(list[Atom] atoms)) = "\<<intercalate(",", [a | Atom a <- atoms])>\>";  

str unparse(empty(Expr expr))                                          = "(no <unparse(expr)>)";
str unparse(atMostOne(Expr expr))                                      = "(lone <unparse(expr)>)";
str unparse(exactlyOne(Expr expr))                                     = "(one <unparse(expr)>)";
str unparse(nonEmpty(Expr expr))                                       = "(some <unparse(expr)>)"; 
str unparse(subset(Expr lhsExpr, Expr rhsExpr))                        = "(<unparse(lhsExpr)> in <unparse(rhsExpr)>)";
str unparse(equal(Expr lhsExpr, Expr rhsExpr))                         = "(<unparse(lhsExpr)> == <unparse(rhsExpr)>)";
str unparse(inequal(Expr lhsExpr, Expr rhsExpr))                       = "(<unparse(lhsExpr)> !== <unparse(rhsExpr)>)";
str unparse(negation(AlleFormula form))                                = "(not <unparse(form)>)";
str unparse(conjunction(AlleFormula lhsForm, AlleFormula rhsForm))     = "(<unparse(lhsForm)> && <unparse(rhsForm)>)";
str unparse(disjunction(AlleFormula lhsForm, AlleFormula rhsForm))     = "(<unparse(lhsForm)> || <unparse(rhsForm)>)";
str unparse(implication(AlleFormula lhsForm, AlleFormula rhsForm))     = "(<unparse(lhsForm)> =\> <unparse(rhsForm)>)";
str unparse(equality(AlleFormula lhsForm, AlleFormula rhsForm))        = "(<unparse(lhsForm)> \<=\> <unparse(rhsForm)>)";  
str unparse(universal(list[VarDeclaration] decls, AlleFormula form))   = "(forall <intercalate(", ", [unparse(d) | VarDeclaration d <- decls])> | <unparse(form)>)";
str unparse(existential(list[VarDeclaration] decls, AlleFormula form)) = "(exists <intercalate(", ", [unparse(d) | VarDeclaration d <- decls])> | <unparse(form)>)";

default str unparse(AlleFormula f) { throw "No unparse function for formula \'<f>\'"; }

str unparse(variable(str name))                                             = name;
str unparse(attributeLookup(Expr expr, str name))                           = "<unparse(expr)>::<name>";
str unparse(transpose(Expr expr))                                           = "(~<unparse(expr)>)";
str unparse(closure(Expr expr))                                             = "(^<unparse(expr)>)";
str unparse(reflexClosure(Expr expr))                                       = "(*<unparse(expr)>)";
str unparse(union(Expr lhs, Expr rhs))                                      = "(<unparse(lhs)>++<unparse(rhs)>)";
str unparse(intersection(Expr lhs, Expr rhs))                               = "(<unparse(lhs)>&<unparse(rhs)>)";
str unparse(difference(Expr lhs, Expr rhs))                                 = "(<unparse(lhs)>\\<unparse(rhs)>)";
str unparse(\join(Expr lhs, Expr rhs))                                      = "(<unparse(lhs)>.<unparse(rhs)>)";
str unparse(accessorJoin(Expr col, Expr select))                            = "(<unparse(col)>[<unparse(select)>])";
str unparse(product(Expr lhs, Expr rhs))                                    = "(<unparse(lhs)>-\><unparse(rhs)>)";
str unparse(ifThenElse(AlleFormula caseForm, Expr thenExpr, Expr elseExpr)) = "(<unparse(caseForm)> ? <unparse(thenExpr)> : <unparse(elseExpr)>)";
str unparse(comprehension(list[VarDeclaration] decls, AlleFormula form))    = "{<intercalate(", ", [unparse(d) | VarDeclaration d <- decls])> | <unparse(form)>}";

default str unparse(Expr exp) { throw "No unparser implemented for \'<exp>\'"; }

str unparse(varDecl(str name, Expr binding)) = "<name>:<unparse(binding)>";

str unparse(relTheory()) = "";