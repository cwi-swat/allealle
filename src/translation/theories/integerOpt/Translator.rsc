module translation::theories::integerOpt::Translator

extend translation::theories::integer::Translator;

import translation::Environment;
import translation::theories::integerOpt::AST;

Formula translateFormula(minimize(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) = translate(m, Command (Formula f) { return minimize(f);}, acf)
  when RelationMatrix m := translateExpression(expr, env, acf);
  
Formula translateFormula(maximize(AlleExpr expr), Environment env, AdditionalConstraintFunctions acf) = translate(m, Command (Formula f) { return maximize(f);}, acf)
    when RelationMatrix m := translateExpression(expr, env, acf);
  
private Formula translate(RelationMatrix m, Command (Formula) opr, AdditionalConstraintFunctions acf) {
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