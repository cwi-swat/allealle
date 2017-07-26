module theories::integerOpt::Translator

extend theories::integer::Translator;

import theories::integerOpt::AST;

Formula translateFormula(minimize(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = translate(expr, Command (Formula f) { return minimize(f);}, env, uni, acf);

Formula translateFormula(maximize(Expr expr), Environment env, Universe uni, AdditionalConstraintFunctions acf) 
  = translate(expr, Command (Formula f) { return maximize(f);}, env, uni, acf);


private Formula translate(Expr expr, Command (Formula) operation, Environment env, Universe uni, AdditionalConstraintFunctions acf) {
  RelationMatrix m = translateExpression(expr, env, uni, acf);
  
  if (size(m) != 1 && arity(m) != 1) {
    throw "Can only minimize or maximize singleton, unary expressions (results of sum)";
  }
  
  if (Index idx <- m, relAndAtt(Formula relFrom, Formula attForm) := m[idx], \int(_) := attForm || intVar(_) := attForm) {
    acf.addAdditionalCommand(operation(attForm));
    return m[idx].relForm;
  } else {
      throw "Can only minimize or maximize a relation with a single, integer attribute selected";
  }
}