module Translator

import logic::Boolean;
import AST;
import Binder;

import IO;

alias FormulaTranslator = logic::Boolean::Formula (AST::Formula, Environment, Universe);
alias ExpressionTranslator = Binding (Expr, Environment, Universe); 
alias SingletonConstructor = Environment (str, Binding, list[Atom]);

alias TranslatorAggregatorFunctions = tuple[FormulaTranslator translateFormula, ExpressionTranslator translateExpression, SingletonConstructor constructSingleton];

data Translator = translator(Environment (Problem) constructEnvironment,
                             bool (AST::Formula) has,
                             Formula (AST::Formula, Environment, Universe, TranslatorAggregatorFunctions) translateFormula,
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
  
    for (Translator translator <- translators, Binding r := translator.translateExpression(expr, env, uni, <translateFormula, translateExpression, constructSingleton>), r != ()) {
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
  
  logic::Boolean::Formula translationResult = (\true() | and(it, r) | AST::Formula f <- p.constraints, logic::Boolean::Formula r := translateFormula(f, env, p.uni));  

  return translationResult;
}

