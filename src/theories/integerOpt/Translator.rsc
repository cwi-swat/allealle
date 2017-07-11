module theories::integerOpt::Translator

extend theories::integer::Translator;

Formula translateFormula(minimize(Expr expr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) 
  = translate(expr, Formula (Formula f) { return minimize(f);}, env, uni, addTheoryConstraint, addAdditionalConstraint);

Formula translateFormula(maximize(Expr expr), Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) 
  = translate(expr, Formula (Formula f) { return maximize(f);}, env, uni, addTheoryConstraint, addAdditionalConstraint);


private Formula translate(Expr expr, Formula (Formula) operation, Environment env, Universe uni, void (set[TheoryFormula]) addTheoryConstraint, void (Formula) addAdditionalConstraint) {
  RelationMatrix m = translateExpression(expr, env, uni, addTheoryConstraint, addAdditionalConstraint);
  
  if (size(m) != 1 && arity(m) != 1) {
    throw "Can only minimize singleton, unary expressions (results of sum)";
  }
  
  Formula result = \true();
  
  for (Index i <- m, form(Formula lhsRelForm, equal(iVar:intVar(str _), Formula _)) <- m[i].ext[0]) {
    result = m[i].relForm;
    addAdditionalConstraint(operation(iVar));
  }
  
  return result;
}