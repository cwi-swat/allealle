module theories::integerOpt::Translator

extend theories::integer::Translator;

import theories::integerOpt::AST;

Formula translateFormula(minimize(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = translate(expr, Command (Formula f) { return minimize(f);}, env, uni, acf);

Formula translateFormula(maximize(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = translate(expr, Command (Formula f) { return maximize(f);}, env, uni, acf);


private Formula translate(Expr expr, Command (Formula) operation, Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationAndAttributes m = translateExpression(expr, env, uni, acf);
  
  if (size(m.relation) != 1 && arity(m) != 1) {
    throw "Can only minimize or maximize singleton, unary expressions (results of sum)";
  }
  
  if (Index idx <- m.att, size(m.att[idx][0]) != 1) {
    throw "Can only minimize or maximize a relation with a single, integer attribute selected";
  }
  
  Formula result = \true();
  
  for (Index idx <- m.relation, str attName <- m.att[idx][0], f:<Formula _, equal(iVar:intVar(str _), Formula _)> <- m.att[idx][0][attName]) {
    result = m.relation[idx];
    acf.addAttributeConstraint(f);
    acf.addAdditionalCommand(operation(iVar));
  }
  
  return result;
}