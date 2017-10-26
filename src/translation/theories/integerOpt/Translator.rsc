module translation::theories::integerOpt::Translator

extend translation::theories::integer::Translator;

import translation::theories::integerOpt::AST;

@memo
Formula translateFormula(minimize(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) 
  = translate(expr, Command (Formula f) { return minimize(f);}, env, acf);

@memo
Formula translateFormula(maximize(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) 
  = translate(expr, Command (Formula f) { return maximize(f);}, env, acf);


private Formula translate(AlleExpr expr, Command (Formula) opr, Environment env, AdditionalConstraintFunctions acf) {
  RelationMatrix m = translateExpression(expr, env, acf);
  
  if (size(m) != 1 && arity(m) != 1) {
    throw "Can only minimize or maximize singleton, unary expressions (results of sum, cardinality, etc)";
  }
  
  if (Index idx <- m, relAndAtt(Formula relFrom, Formula attForm) := m[idx], isIntForm(attForm)) {
    acf.addAdditionalCommand(opr(attForm));
    return m[idx].relForm;
  } else {
      throw "Can only minimize or maximize a relation with a single, integer attribute selected";
  }
}