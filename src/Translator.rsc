module Translator

import logic::Boolean;
import AST;
import Binder;

import IO;

alias FormulaTranslator = Formula (AlleFormula, Environment, Universe);
alias ExpressionTranslator = Binding (Expr, Environment, Universe); 
alias SingletonConstructor = Environment (str, Binding, list[Atom]);

alias TranslatorAggregatorFunctions = tuple[FormulaTranslator translateFormula, ExpressionTranslator translateExpression, SingletonConstructor constructSingleton];

data Translator = translator(Environment (Problem) constructEnvironment,
                             bool (AlleFormula) has,
                             Formula (AlleFormula, Environment, Universe, TranslatorAggregatorFunctions) translateFormula,
                             Binding (Expr, Environment, Universe, TranslatorAggregatorFunctions) translateExpression,
                             Environment (str, Binding, list[Atom]) constructSingletonBinding);

Environment createInitialEnvironment(Problem p, list[Translator] translators) {
  Environment env = ();
  
  for (Translator translator <- translators) {
    Environment partialEnv = translator.constructEnvironment(p);
    for (str relName <- partialEnv) {
      env[relName] = (relName in env) ? env[relName] + partialEnv[relName] : partialEnv[relName];
    }   
  }
  
  return env;
}
                               
Formula translate(Problem p, Environment env, list[Translator] translators) {
  @memo
  tuple[Formula (AlleFormula, Environment, Universe), Binding (Expr, Environment, Universe), Environment (str, Binding, list[Atom])] aggregates() = <translateFormula, translateExpression, constructSingleton>;  
  
  Formula translateFormula(AlleFormula form, Environment env, Universe uni) {
    Formula result = \false(); 
    bool alreadyTranslated = false;
    
    for (Translator translator <- translators, translator.has(form), Formula r := translator.translateFormula(form, env, uni, aggregates())) {
      if (alreadyTranslated) {
        throw "Error while translating the formula \'<form>\'; more then one translator translated the formula";
      }
      
      result = r;
      alreadyTranslated = true; 
    }
    
    return result;
  }
  
  Binding translateExpression(Expr expr, Environment env, Universe uni) {
    Binding result = ();
  
    for (Translator translator <- translators, Binding r := translator.translateExpression(expr, env, uni, aggregates()), r != ()) {
      if (result != ()) {
        throw "Error while translating the expr \'<expr>\'; more then one translator translated the expression"; 
      }
      
      result = r; 
    }
    
    return result;
  }
  
  Environment constructSingleton(str newVarName, Binding orig, list[Atom] vector) {
    Environment singleton = ();
  
    for (Translator translator <- translators) {
      Environment partialSingleton = translator.constructSingletonBinding(newVarName, orig, vector);
      for (str relName <- partialSingleton) {
        singleton[relName] = (relName in singleton) ? singleton[relName] + partialSingleton[relName] : partialSingleton[relName];
      }   
    }
  
    return singleton;
  }
  
  Formula translationResult = (\true() | and(it, r) | AlleFormula f <- p.constraints, Formula r := translateFormula(f, env, p.uni));  

  return translationResult;
}

