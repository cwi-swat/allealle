module ide::UnicodeRewriter

import ide::CombinedSyntax;
import ide::rewrite::PTDiff;

import ParseTree;
import IO;

lrel[loc,str] unicodeRewrite(&T<:Tree input) { 
  output = unicodeRewriteTree(input);   
  
  if ("<input>" == "<output>") {
    return [];
  } else {  
    return [<input@\loc,"<output>">];
  }
    
  //diff = ptDiff(input, parse(#start[Problem], "<output>", input@\loc));
  //return diff;
}

&T<:Tree unicodeRewriteTree(&T<:Tree input) {
  return visit(input) {
    case (AlleFormula)`not <AlleFormula form>` => (AlleFormula)`¬ <AlleFormula form>` 
    case (AlleFormula)`<AlleExpr lhsExpr> in <AlleExpr rhsExpr>` => (AlleFormula)`<AlleExpr lhsExpr> ⊆ <AlleExpr rhsExpr>`
    case (AlleFormula)`exists <{VarDeclaration ","}+ decls> | <AlleFormula form>` => (AlleFormula)`∃ <{VarDeclaration ","}+ decls> | <AlleFormula form>`
    case (AlleFormula)`forall <{VarDeclaration ","}+ decls> | <AlleFormula form>` => (AlleFormula)`∀ <{VarDeclaration ","}+ decls> | <AlleFormula form>`
    case (AlleFormula)`<AlleExpr lhsExpr> != <AlleExpr rhsExpr>` => (AlleFormula)`<AlleExpr lhsExpr> ≠ <AlleExpr rhsExpr>`
    case (AlleFormula)`<AlleFormula lhsForm> && <AlleFormula rhsForm>` => (AlleFormula)`<AlleFormula lhsForm> ∧ <AlleFormula rhsForm>`
    case (AlleFormula)`<AlleFormula lhsForm> || <AlleFormula rhsForm>` => (AlleFormula)`<AlleFormula lhsForm> ∨ <AlleFormula rhsForm>` 
    case (AlleFormula)`<AlleFormula lhsForm> =\> <AlleFormula rhsForm>` => (AlleFormula)`<AlleFormula lhsForm> ⇒ <AlleFormula rhsForm>`
    case (AlleFormula)`<AlleFormula lhsForm> \<=\> <AlleFormula rhsForm>` => (AlleFormula)`<AlleFormula lhsForm> ⇔ <AlleFormula rhsForm>`
    case (AlleExpr)`<AlleExpr lhs> + <AlleExpr rhs>` => (AlleExpr)`<AlleExpr lhs> ∪ <AlleExpr rhs>`
    case (AlleExpr)`<AlleExpr lhs> & <AlleExpr rhs>` => (AlleExpr)`<AlleExpr lhs> ∩ <AlleExpr rhs>`
    case (AlleExpr)`<AlleExpr lhs> |x| <AlleExpr rhs>` => (AlleExpr)`<AlleExpr lhs> ⨝ <AlleExpr rhs>`
    case (AlleExpr)`<AlleExpr lhs> - <AlleExpr rhs>` => (AlleExpr)`<AlleExpr lhs> ∖ <AlleExpr rhs>`
    case (AlleExpr)`<AlleExpr lhs> x <AlleExpr rhs>` => (AlleExpr)`<AlleExpr lhs> ⨯ <AlleExpr rhs>`
    case (VarDeclaration)`<RelVar var> : <AlleExpr expr>` => (VarDeclaration)`<RelVar var> ∈ <AlleExpr expr>` 
  }
}
