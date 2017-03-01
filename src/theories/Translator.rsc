module theories::Translator

import logic::Boolean;
import theories::AST;
import theories::Binder;

import IO;

Environment createInitialEnvironment(Problem p) = (rb.relName:createRelationalMapping(rb) | RelationalBound rb <- p.bounds);
                                                   
default Binding createRelationalMapping(RelationalBound rb) { throw "Unable to construct a relational mapping for relational bounds \'<rb>\'";}                                                   
                                                                                            
Formula translate(Problem p, Environment env) = (\true() | and(it, r) | AlleFormula f <- p.constraints, Formula r := translateFormula(f, env, p.uni));  

Environment constructSingleton(str newVarName, list[Atom] vector, Binding origBinding) {
  Binding singletonBinding = (() | it + constructSingletonWithTheory(t, vector, origBinding[idx]) | Index idx:<Theory t, vector> <- origBinding); 
  
  return (newVarName: singletonBinding);  
}
 
default Binding constructSingletonWithTheory(Theory theory, list[Atom] vector, Formula originalValue) { throw "Unable to construct a singelton variable for theory \'<theory>\' with value \'<originalValue>\'";}

default Formula translateFormula(AlleFormula f, Environment env, Universe uni) { throw "Translation of formula \'<f>\' not supported"; }
default Binding translateExpression(Expr expr, Environment env, Universe uni) { throw "Translation of expression \'<expr>\' not supported"; }

