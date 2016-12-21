module Translator

import logic::Boolean;
import AST;
import Binder;

alias FormulaTranslator = logic::Boolean::Formula (AST::Formula, Environment, Universe);
alias ExpressionTranslator = Binding (Expr, Environment, Universe); 

data Translator = translator(Environment (Problem) constructEnvironment,
                             bool (AST::Formula) has,
                             Formula (AST::Formula, Environment, Universe, FormulaTranslator, ExpressionTranslator) translateFormula,
                             Binding (Expr, Environment, Universe, FormulaTranslator, ExpressionTranslator) translateExpression);

Environment createInitialEnvironment(Problem p, list[Translator] translators) = (() | it + translator.constructEnvironment(p) | Translator translator <- translators);
                               
logic::Boolean::Formula translate(Problem p, Environment env, list[Translator] translators) {
  logic::Boolean::Formula translateFormula(AST::Formula form, Environment env, Universe uni) = 
    (\true() | and(it, r) | Translator translator <- translators, Formula r := translator.translateFormula(form, env, uni, translateFormula, translateExpression));
  
  Binding translateExpression(AST::Expr expr, Environment env, Universe uni) =
    (() | it + r | Translator translator <- translators, Binding r := translator.translateExpression(expr, env, uni, translateFormula, translateExpression));


  logic::Boolean::Formula translationResult = (\true() | and(it, r) | AST::Formula f <- p.constraints, 
                                                                      Translator translator <- translators, 
                                                                      translator.has(f), 
                                                                      logic::Boolean::Formula r := translator.translateFormula(f, env, p.uni, translateFormula, translateExpression));  

  return translationResult;
}

