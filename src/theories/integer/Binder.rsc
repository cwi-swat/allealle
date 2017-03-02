module theories::integer::Binder


import theories::Binder;
import theories::relational::Binder;
import logic::Integer;
import theories::integer::AST;

Binding multiply(Binding lhs, Binding rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return multiplication(l,r); });
Binding divide(Binding lhs, Binding rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return division(l,r); }); 
Binding add(Binding lhs, Binding rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return addition(l,r); });
Binding substract(Binding lhs, Binding rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return substraction(l,r); }); 
Binding gt(Binding lhs, Binding rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return gt(l,r); });
Binding gte(Binding lhs, Binding rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return gte(l,r); });
Binding lt(Binding lhs, Binding rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return lt(l,r); });
Binding lte(Binding lhs, Binding rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return lte(l,r); });
Binding lte(Binding lhs, Binding rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return lte(l,r); });
Binding equal(Binding lhs, Binding rhs) = translate(lhs, rhs, Formula (Formula l, Formula r) { return equal(l,r); });

private Binding translate(Binding lhs, Binding rhs, Formula (Formula, Formula) operation) 
  = (<intTheory(), a.vector + b.vector>:operation(lhs[a], rhs[b]) | Index a <- lhs, a.theory == intTheory(), Index b <- rhs, b.theory == intTheory());
