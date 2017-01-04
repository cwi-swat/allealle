module Translator

import logic::Boolean;
import AST;
import Binder;

alias FormulaTranslator = logic::Boolean::Formula (AST::Formula, Environment, Universe);
alias ExpressionTranslator = Binding (Expr, Environment, Universe); 
alias SingletonConstructor = Environment (str, Binding, list[Atom]);

alias TranslatorAggregatorFunctions = tuple[FormulaTranslator translateFormula, ExpressionTranslator translateExpression, SingletonConstructor constructSingleton];

data Translator = translator(Environment (Problem) constructEnvironment,
                             bool (AST::Formula) has,
                             Formula (AST::Formula, Environment, Universe, TranslatorAggregatorFunctions) translateFormula,
                             Binding (Expr, Environment, Universe, TranslatorAggregatorFunctions) translateExpression,
                             Environment (str, Binding, list[Atom]) constructSingletonBinding);

Environment createInitialEnvironment(Problem p, list[Translator] translators) = (() | it + translator.constructEnvironment(p) | Translator translator <- translators);
                               
logic::Boolean::Formula translate(Problem p, Environment env, list[Translator] translators) {
  
  logic::Boolean::Formula translateFormula(AST::Formula form, Environment env, Universe uni) {
    Formula result = \false(); 
    bool alreadyTranslated = false;
    
    for (Translator translator <- translators, translator.has(form), Formula r := translator.translateFormula(form, env, uni, <translateFormula, translateExpression, constructSingleton>)) {
      if (alreadyTranslated) {
        throw "Error while translating the formula \'<form>\'; more then one translator translated the formula";
      }
      
      result = r;
      alreadyTranslated = true; 
    }
    
    return result;
  }
  
  Binding translateExpression(AST::Expr expr, Environment env, Universe uni) {
    Binding result = ();
  
    for (Translator translator <- translators, Binding r := translator.translateExpression(expr, env, uni, <translateFormula, translateExpression, constructSingleton>)) {
      if (result != () && r != ()) {
        throw "Error while translating the expr \'<expr>\'; more then one translator translated the expression"; 
      }
      
      result = r; 
    }
    
    return result;
  }
    
  Environment constructSingleton(str newVarName, Binding orig, list[Atom] vector) =
    (() | it + r | Translator translator <- translators, Environment r := translator.constructSingletonBinding(newVarName, orig, vector));

  logic::Boolean::Formula translationResult = (\true() | and(it, r) | AST::Formula f <- p.constraints, 
                                                                      Translator translator <- translators, 
                                                                      translator.has(f), 
                                                                      logic::Boolean::Formula r := translator.translateFormula(f, env, p.uni, <translateFormula, translateExpression, constructSingleton>));  

  return translationResult;
}

