module theories::integerOpt::PreProcessor

extend theories::integer::PreProcessor;

import theories::integerOpt::AST;

AlleFormula transform(minimize(Expr expr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = minimize(transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));

AlleFormula transform(maximize(Expr expr), Env env, Universe uni, str () newResultAtom, void (str, set[AtomDecl], set[list[AtomDecl]]) addRelation, void (AlleFormula) addConstraint, str () newRelNr)
  = maximize(transform(expr, env, uni, newResultAtom, addRelation, addConstraint, newRelNr));
   