module translation::Imploder

import translation::Syntax;
import translation::AST;

import ParseTree;
import String;

translation::AST::Problem implodeProblem(translation::Syntax::Problem p) 
  = problem([implode(r) | r <- p.relations], [implode(c) | c <- p.constraints]); 

translation::AST::RelationDef implode((Relation)`<RelVar v> (<{HeaderAttribute ","}+ header>) <RelationalBound bounds>`) 
  = relation("<v>", [implode(h) | h <- header], implode(bounds));
 
translation::AST::HeaderAttribute implode((HeaderAttribute)`<AttributeName name> : <Domain d>`)
  = header("<name>", implode(d));

translation::AST::HeaderAttribute implode((HeaderAttribute)`_ : <Domain d>`)
  = header("_", implode(d));

translation::AST::RelationalBound implode((RelationalBound)`= { <{Tuple ","}* tuples>}`) 
  = exact([implode(t) | t <- tuples]);

translation::AST::RelationalBound implode((RelationalBound)`\<= { <{Tuple ","}+ upper> }`) 
  = atMost([implode(t) | t <- upper]);

translation::AST::RelationalBound implode((RelationalBound)`\>= { <{Tuple ","}+ lower> } \<= { <{Tuple ","}+ upper> }`) 
  = atLeastAtMost([implode(t) | t <- lower],[implode(t) | t <- upper]);

translation::AST::AlleTuple implode((Tuple)`\< <{Value ","}+ values> \>`)
  = tup([implode(v) | v <- values]);
  
translation::AST::AlleTuple implode((Tuple)`\< <{RangedValue ","}+ from> \>..\<<{RangedValue ","}+ to>\>`)
  = range([implode(rv) | rv <- from], [implode(rv) | rv <- to]); 

translation::AST::AlleValue implode((Value)`<Idd i>`)
  = id("<i>");   

translation::AST::AlleValue implode((Value)`<Literal l>`)
  = lit(implode(l));  
 
translation::AST::AlleValue implode((Value)`?`)
  = hole();  

translation::AST::RangedValue implode((RangedValue)`<RangedId prefix><RangedNr numm>`)
  = id("<prefix>",toInt("<numm>"));  

translation::AST::RangedValue implode((RangedValue)`<RangedId i>`)
  = idOnly("<i>");  

translation::AST::RangedValue implode((RangedValue)`<Literal l>`)
  = templateLit(implode(l));   

translation::AST::RangedValue implode((RangedValue)`?`)
  = templateHole();  
  
translation::AST::Domain implode((Domain)`id`)
  = id();  

translation::AST::Domain implode((Domain)`FAIL`)
  = \fail();    

translation::AST::AlleLiteral implode((Literal)`none`)
  = none();

translation::AST::AlleFormula implode((AlleFormula)`( <AlleFormula form> )`) 
  = implode(form);

translation::AST::AlleFormula implode(f:(AlleFormula)`¬ <AlleFormula form>`) 
  = negation(implode(form), origLoc=f@\loc);
  
translation::AST::AlleFormula implode(f:(AlleFormula)`no <AlleExpr expr>`)
  = empty(implode(expr), origLoc=f@\loc);
    
translation::AST::AlleFormula implode(f:(AlleFormula)`lone <AlleExpr expr>`)
  = atMostOne(implode(expr), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`one <AlleExpr expr>`)
  = exactlyOne(implode(expr), origLoc=f@\loc);
  
translation::AST::AlleFormula implode(f:(AlleFormula)`some <AlleExpr expr>`)
  = nonEmpty(implode(expr), origLoc=f@\loc);
  
translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleExpr lhsExpr> ⊆ <AlleExpr rhsExpr>`)
  = subset(implode(lhsExpr),implode(rhsExpr), origLoc=f@\loc);
  
translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleExpr lhsExpr> = <AlleExpr rhsExpr>`)
  = equal(implode(lhsExpr),implode(rhsExpr), origLoc=f@\loc);
  
translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleExpr lhsExpr> ≠ <AlleExpr rhsExpr>`)
  = inequal(implode(lhsExpr),implode(rhsExpr), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleFormula lhsExpr> ∧ <AlleFormula rhsExpr>`)
  = conjunction(implode(lhsExpr),implode(rhsExpr), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleFormula lhsExpr> ∨ <AlleFormula rhsExpr>`)
  = disjunction(implode(lhsExpr),implode(rhsExpr), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleFormula lhsExpr> ⇒ <AlleFormula rhsExpr>`)
  = implication(implode(lhsExpr),implode(rhsExpr), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleFormula lhsExpr> ⇔ <AlleFormula rhsExpr>`)
  = equality(implode(lhsExpr),implode(rhsExpr), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`let <{VarDeclaration ","}+ decls> | <AlleFormula form>`)
  = let([implode(d) | d <- decls], implode(form), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`∀ <{VarDeclaration ","}+ decls> | <AlleFormula form>`)
  = universal([implode(d) | d <- decls], implode(form), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`∃ <{VarDeclaration ","}+ decls> | <AlleFormula form>`)
  = existential([implode(d) | d <- decls], implode(form), origLoc=f@\loc);

translation::AST::VarDeclaration implode((VarDeclaration)`<RelVar var> ∈ <AlleExpr expr>`)
  = varDecl("<var>", implode(expr)); 
  
translation::AST::AlleExpr implode((AlleExpr)`( <AlleExpr expr> )`)
  = implode(expr);
  
translation::AST::AlleExpr implode((AlleExpr)`<RelVar v>`)
  = relvar("<v>");
 
translation::AST::AlleExpr implode((AlleExpr)`<Literal l>`)
  = lit(implode(l));

translation::AST::AlleExpr implode((AlleExpr)`[<{Rename ","}+ ren>] <AlleExpr expr>`)
  = rename(implode(expr), [implode(r) | r <- ren]);

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr expr>[<{AttributeName ","}+ atts>]`)
  = project(implode(expr), ["<a>" | a <- atts]);

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr expr> where <Criteria criteria>`)
  = restriction(implode(expr), implode(restriction));
  
translation::AST::AlleExpr implode((AlleExpr)`~<AlleExpr expr>`)
  = transpose(implode(expr));
translation::AST::AlleExpr implode((AlleExpr)`~<TupleAttributeSelection tas> <AlleExpr expr>`)
  = transpose(implode(tas), implode(expr));
    
translation::AST::AlleExpr implode((AlleExpr)`^<TupleAttributeSelection tas> <AlleExpr expr>`)
  = closure(implode(tas), implode(expr));

translation::AST::AlleExpr implode((AlleExpr)`*<TupleAttributeSelection tas> <AlleExpr expr>`)
  = reflexClosure(implode(tas), implode(expr));
  
translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> ⨝ <AlleExpr rhs>`)
  = naturalJoin(implode(lhs), implode(rhs)); 
  
translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> ∪ <AlleExpr rhs>`)
  = union(implode(lhs), implode(rhs));

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> ∩ <AlleExpr rhs>`)
  = intersection(implode(lhs), implode(rhs));
  
translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> ∖ <AlleExpr rhs>`)
  = difference(implode(lhs), implode(rhs));
  
translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> ⨯ <AlleExpr rhs>`)
  = product(implode(lhs), implode(rhs));
 
translation::AST::TupleAttributeSelection implode ((TupleAttributeSelection)`\<<AttributeName first>,<AttributeName second>\>`) 
  = order("<first>","<second>");
  
translation::AST::Rename implode((Rename)`<AttributeName new> / <AttributeName orig>`) 
  = rename("<new>","<orig>");

translation::AST::Criteria implode((Criteria)`( <Criteria cr> )`) 
  = implode(cr);    
 
translation::AST::Criteria implode((Criteria)`not <Criteria r>`) 
  = not(implode(r));    

translation::AST::Criteria implode((Criteria)`<CriteriaExpr lhs> = <CriteriaExpr rhs>`) 
  = equal(implode(lhs),implode(rhs));

translation::AST::Criteria implode((Criteria)`<Criteria lhs> && <Criteria rhs>`) 
  = and(implode(lhs),implode(rhs));
  
translation::AST::Criteria implode((Criteria)`<Criteria lhs> || <Criteria rhs>`) 
  = or(implode(lhs),implode(rhs));
 
translation::AST::CriteriaExpr implode((CriteriaExpr)`<AttributeName att>`) 
  = att("<att>");

translation::AST::CriteriaExpr implode((CriteriaExpr)`<Literal l>`) 
  = lit(implode(l));
   
default &T implode(&R production) { throw "Unable to implode production \'<production>\'. No implode function implemented"; }
