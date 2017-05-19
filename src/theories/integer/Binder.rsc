module theories::integer::Binder

extend theories::Binder;

import logic::Integer;
import theories::integer::AST;

RelationMatrix multiply(RelationMatrix lhs, RelationMatrix rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return multiplication(l,r); });
RelationMatrix divide(RelationMatrix lhs, RelationMatrix rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return division(l,r); }); 
RelationMatrix modd(RelationMatrix lhs, RelationMatrix rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return modulo(l,r); }); 
RelationMatrix add(RelationMatrix lhs, RelationMatrix rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return addition(l,r); });
RelationMatrix substract(RelationMatrix lhs, RelationMatrix rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return substraction(l,r); }); 
 
private ExtensionEncoding performOperation(ExtensionEncoding lhs, ExtensionEncoding rhs, Formula (Formula, Formula) operation) {
  //ExtensionEncoding result = ();
  //
  //for (int i <- lhs) {
  //  if (i notin rhs) { throw "Unable to combine to Integer extensions with different arities together. Lhs = \'<lhs>\', Rhs = \'<rhs>\'"; }
  //  result[i] = operation(lhs[i], rhs[i]);  
  //}
  //
  //return result;
  
  return ();
} 
 
private RelationMatrix translate(RelationMatrix lhs, RelationMatrix rhs, Formula (Formula, Formula) operation) = (); 
  //= (currentLhs + currentRhs : <val, (intTheory() : performOperation(lhs[currentLhs].ext[intTheory()], rhs[currentRhs].ext[intTheory()], operation))> | 
  //    Index currentLhs <- lhs, 
  //    lhs[currentLhs].relForm != \false(),
  //    intTheory() in lhs[currentLhs].ext,
  //    Index currentRhs <- rhs, 
  //    rhs[currentRhs].relForm != \false(),
  //    intTheory() in rhs[currentRhs].ext,
  //    Formula val := and(lhs[currentLhs].relForm, rhs[currentRhs].relForm), 
  //    val !:= \false());       