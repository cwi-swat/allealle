module relational::Translator

import Translator; 
import relational::AST;
import relational::Binder;

import IO;
import List; 
import Relation;
import Map;
import Set;
 
import logic::Propositional;

Translator getRelationalTranslator() = translator(createInitialEnvironment, has, translateFormula, translateExpr, constructSingletonBinding);

Environment createInitialEnvironment(Problem p) 
  = (rb.relName:createRelationalMapping(rb) | RelationalBound rb <- p.bounds);

private Binding createRelationalMapping(relationalBound(str relName, int arity, list[Tuple] lowerBounds, list[Tuple] upperBounds)) =
  createRelationalMapping(relationalBoundWithTheory(relName, relational(), arity, lowerBounds, upperBounds));

private Binding createRelationalMapping(relationalBoundWithTheory(str relName, relational(), int arity, list[Tuple] lb, list[Tuple] ub)) {
  str idxToStr(list[Atom] idx) = intercalate("_", idx);
  
  Binding result = (<relational(), idx> : \true() | \tuple(list[Atom] idx) <- lb);
  result += (<relational(), idx> : var("<relName>_<idxToStr(idx)>") | \tuple(list[Atom] idx) <- ub, <relational(), idx> notin result);
  
  return result;
} 

bool has(empty(Expr _)) = true;
bool has(atMostOne(Expr _)) = true;
bool has(exactlyOne(Expr _)) = true;
bool has(nonEmpty(Expr _)) = true;
bool has(subset(Expr _, Expr _)) = true;
bool has(equal(Expr _, Expr _)) = true;
bool has(negation(Formula _)) = true;
bool has(conjunction(Formula _, Formula _)) = true;
bool has(disjunction(Formula _, Formula _)) = true;
bool has(implication(Formula _, Formula _)) = true;
bool has(equality(Formula _, Formula _)) = true;
bool has(universal(list[VarDeclaration] _, Formula _)) = true;
bool has(existential(list[VarDeclaration] _, Formula _) ) = true;
default bool has(Formula _) = false;

Formula translateFormula(empty(Expr expr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) 
  = \not(aggregate.translateFormula(nonEmpty(expr), env, uni));

Formula translateFormula(atMostOne(Expr expr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate)   
  = \or(aggregate.translateFormula(empty(expr), env, uni), aggregate.translateFormula(exactlyOne(expr), env, uni));

Formula translateFormula(exactlyOne(Expr expr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate)  
  = (\false() | \or(it, \and(m[x], (\true() | \and(it, \not(m[y])) | Index y <- m, relational() := y.theory, y != x))) | Index x <- m)    
  when Binding m := aggregate.translateExpression(expr, env, uni);

Formula translateFormula(nonEmpty(Expr expr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate)      
  = (\false() | \or(it,  m[x]) | Index x <- m, relational() := x.theory)
  when Binding m := aggregate.translateExpression(expr, env, uni);

Formula translateFormula(subset(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) 
  = m == () ? \false() : (\true() | \and(it, m[x]) | Index x <- m, relational() := x.theory)
  when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
     Binding rhs := aggregate.translateExpression(rhsExpr, env, uni),
     Binding m :=(idx:\or({\not(lhsVal), rhsVal}) | Index idx <- (lhs + rhs), relational() := idx.theory, Formula lhsVal := ((idx in lhs) ? lhs[idx] : \false()), Formula rhsVal := ((idx in rhs) ? rhs[idx] : \false())); 
     
Formula translateFormula(equal(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate)
  = \and(aggregate.translateFormula(subset(lhsExpr, rhsExpr), env, uni), aggregate.translateFormula(subset(rhsExpr, lhsExpr), env, uni));
  
Formula translateFormula(negation(Formula form), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) 
  = \not(aggregate.translateFormula(form, env, uni));
  
Formula translateFormula(conjunction(Formula lhsForm, Formula rhsForm), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate)
  = \and(aggregate.translateFormula(lhsForm, env, uni), aggregate.translateFormula(rhsForm, env, uni));
  
Formula translateFormula(disjunction(Formula lhsForm, Formula rhsForm), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate)
  = \or(aggregate.translateFormula(lhsForm, env, uni), aggregate.translateFormula(rhsForm, env, uni));
  
Formula translateFormula(implication(Formula lhsForm, Formula rhsForm), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate)
  = \or(\not(aggregate.translateFormula(lhsForm, env, uni)), aggregate.translateFormula(rhsForm, env, uni));
  
Formula translateFormula(equality(Formula lhsForm, Formula rhsForm), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate)
  = \or(\and(aggregate.translateFormula(lhsForm, env, uni),  aggregate.translateFormula(rhsForm, env, uni)), \and(\not(aggregate.translateFormula(lhsForm, env, uni)), \not(aggregate.translateFormula(rhsForm, env, uni))));

Formula translateFormula(universal(list[VarDeclaration] decls, Formula form), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) 
  = \and({\or({\not(m[x]), aggregate.translateFormula(f, env + aggregate.constructSingleton(hd.name, m, x.vector), uni)}) | Index x <- m, relational() := x.theory, Formula f := (([] == t) ? form : universal(t, form))})
  when [VarDeclaration hd, *t] := decls,
       Binding m := aggregate.translateExpression(hd.binding, env, uni);
   
Formula translateFormula(existential(list[VarDeclaration] decls, Formula form), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate)
  = \or({\and({m[x], aggregate.translateFormula(f, env + aggregate.constructSingleton(hd.name, m, x.vector), uni)}) | Index x <- m, relational() := x.theory, Formula f := (([] == t) ? form : existential(t, form))}) 
  when [VarDeclaration hd, *t] := decls,
       Binding m := aggregate.translateExpression(hd.binding, env, uni);
        
default Formula translateFormula(Formula f, Environment env, Universe uni) { throw "Translation of formula \'<f>\' with function \'<translateFormula>\' not yet implemented";}

@memo
Environment constructSingletonBinding(str newVarName, Binding orig, list[Atom] vector) = (newVarName:(<relational(), vector>:\true())) when <relational(), vector> <- orig; 
@memo
default Environment constructSingletonBinding(str _, Binding _, list[Atom] _) = ();

Binding translateExpr(variable(str name), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = env[name];

Binding translateExpr(transpose(Expr expr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = transpose(m, uni)
  when Binding m := aggregate.translateExpression(expr, env, uni); 

Binding translateExpr(closure(Expr expr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = transitiveClosure(m, uni)
  when Binding m := aggregate.translateExpression(expr, env, uni);
     
Binding translateExpr(reflexClosure(Expr expr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = reflexiveTransitiveClosure(m, uni)
  when Binding m := aggregate.translateExpression(expr, env, uni);
    
Binding translateExpr(union(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = disjunction(lhs,rhs)  
  when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
       Binding rhs := aggregate.translateExpression(rhsExpr, env, uni);
  
Binding translateExpr(intersection(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = conjunction(lhs, rhs)
  when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
       Binding rhs := aggregate.translateExpression(rhsExpr, env, uni);

Binding translateExpr(difference(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = 
  (x:\and(lhs[x],rhsVal) | Index x <- lhs, x.theory == relational(), Formula rhsVal := ((x notin rhs) ? \true() : \not(rhs[x])))
  when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
       Binding rhs := aggregate.translateExpression(rhsExpr, env, uni);

Binding translateExpr(\join(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = \join(lhs, rhs) 
  when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
       Binding rhs := aggregate.translateExpression(rhsExpr, env, uni);

Binding translateExpr(accessorJoin(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = aggregate.translateExpression(\join(rhsExpr, lhsExpr), env, uni);
    
Binding translateExpr(product(Expr lhsExpr, Expr rhsExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) = product(lhs, rhs)
  when Binding lhs := aggregate.translateExpression(lhsExpr, env, uni),
       Binding rhs := aggregate.translateExpression(rhsExpr, env, uni);

Binding translateExpr(ifThenElse(Formula caseForm, Expr thenExpr, Expr elseExpr), Environment env, Universe uni, TranslatorAggregatorFunctions aggregate)
   = (idx:ite(translateFormula(caseForm, env, uni),p[idx],q[idx]) | Index idx <- p)
  when Binding p := aggregate.translateExpression(thenExpr, env, uni),
       Binding q := aggregate.translateExpression(elseExpr, env, uni);
     
//Binding translateExpr(comprehension(list[VarDeclaration] decls, Formula form), Environment env) {
//  Index flatten([<Atom a, relTheory()>]) = <a, relTheory()>;
//  Index flatten([<Atom a, relTheory()>, <Atom b, relTheory()>]) = <a,b, relTheory()>;
//  Index flatten([<Atom a, relTheory()>, <Atom b, relTheory()>, <Atom c, relTheory()>]) = <a,b,c, relTheory()>;
//  
//  Binding getVal(list[Index] currentIndex, Environment extendedEnv, int currentDecl, Formula declConstraints) {
//    if (currentDecl == size(decls)) {
//      return (flatten(currentIndex):\and(declConstraints, translateFormula(form, env + extendedEnv)));
//    }
//    
//    VarDeclaration decl = decls[currentDecl];
//    Binding m = translateExpr(decl.binding, env + extendedEnv);
//        
//    Binding result = ();
//    for (Index idx <- m) {
//      result += getVal([*currentIndex, idx], extendedEnv + (decl.name:getSingletonBinding(idx)), currentDecl + 1, \and(declConstraints, m[idx]));
//    }   
//    
//    return result; 
//  }
//  
//  Binding result = getVal([], env, 0, \true());
//  
//  return result;  
//}
  
default Binding translateExpr(Expr e, Environment env, Universe uni, TranslatorAggregatorFunctions aggregate) { throw "Translation of expression \'<e>\' not yet implemented";}
