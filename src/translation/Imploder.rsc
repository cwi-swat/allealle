module translation::Imploder

import translation::Syntax;
import translation::AST;
import translation::DomainResolver;

import ParseTree;
import String;

translation::AST::Problem implodeProblem(translation::Syntax::Problem p, ResolvedDomains dom) 
  = problem([implode(r,dom) | r <- p.relations], [implode(c,dom) | c <- p.constraints]); 

translation::AST::RelationDef implode((RelationDef)`<RelVar v> (<{HeaderAttribute ","}+ header>) <RelationalBound bounds>`, ResolvedDomains dom) 
  = relation("<v>", [implode(h,dom) | h <- header], implode(bounds,dom));
 
translation::AST::HeaderAttribute implode((HeaderAttribute)`<AttributeName name> : <Domain d>`, ResolvedDomains dom)
  = header("<name>", implode(d, dom));

translation::AST::HeaderAttribute implode((HeaderAttribute)`_ : <Domain d>`, ResolvedDomains dom)
  = header("_", implode(d, dom));

translation::AST::RelationalBound implode((RelationalBound)`= { <{Tuple ","}* tuples>}`, ResolvedDomains dom) 
  = exact([implode(t,dom) | t <- tuples]);

translation::AST::RelationalBound implode((RelationalBound)`\<= { <{Tuple ","}+ upper> }`, ResolvedDomains dom) 
  = atMost([implode(t,dom) | t <- upper]);

translation::AST::RelationalBound implode((RelationalBound)`\>= { <{Tuple ","}+ lower> } \<= { <{Tuple ","}+ upper> }`, ResolvedDomains dom) 
  = atLeastAtMost([implode(t,dom) | t <- lower],[implode(t,dom) | t <- upper]);

translation::AST::Tuple implode((Tuple)`\< <{Value ","}+ values> \>`, ResolvedDomains dom)
  = tup([implode(v,dom) | v <- values]);
  
translation::AST::Tuple implode((Tuple)`\< <{RangedValue ","}+ from> \>..\<<{RangedValue ","}+ to>\>`, ResolvedDomains dom)
  = range([implode(rv,dom) | rv <- from], [implode(rv,dom) | rv <- to]); 

translation::AST::Value implode((Value)`<Idd i>`, ResolvedDomains dom)
  = id("<i>");   

translation::AST::Value implode((Value)`<Literal l>`, ResolvedDomains dom)
  = lit(implode(l,dom));  
 
translation::AST::Value implode((Value)`?`, ResolvedDomains dom)
  = hole();  

translation::AST::RangedValue implode((RangedValue)`<RangedId prefix><RangedNr numm>`, ResolvedDomains dom)
  = id("<prefix>",toInt("<numm>"));  

translation::AST::RangedValue implode((RangedValue)`<RangedId i>`, ResolvedDomains dom)
  = idOnly("<i>");  

translation::AST::RangedValue implode((RangedValue)`<Literal l>`, ResolvedDomains dom)
  = templateLit(implode(l,dom));   

translation::AST::RangedValue implode((RangedValue)`?`, ResolvedDomains dom)
  = templateHole();  
  
translation::AST::Domain implode((Domain)`id`, ResolvedDomains dom)
  = id();  

translation::AST::Domain implode((Domain)`FAIL`, ResolvedDomains dom)
  = \fail();    

translation::AST::Literal implode((Literal)`none`, ResolvedDomains dom)
  = none();

translation::AST::AlleFormula implode((AlleFormula)`( <AlleFormula form> )`, ResolvedDomains dom) 
  = implode(form, dom);

translation::AST::AlleFormula implode(f:(AlleFormula)`not <AlleFormula form>`, ResolvedDomains dom) 
  = negation(implode(form, dom), origLoc=f@\loc);
  
translation::AST::AlleFormula implode(f:(AlleFormula)`no <AlleExpr expr>`, ResolvedDomains dom)
  = empty(implode(expr,dom), origLoc=f@\loc);
    
translation::AST::AlleFormula implode(f:(AlleFormula)`lone <AlleExpr expr>`, ResolvedDomains dom)
  = atMostOne(implode(expr,dom), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`one <AlleExpr expr>`, ResolvedDomains dom)
  = exactlyOne(implode(expr,dom), origLoc=f@\loc);
  
translation::AST::AlleFormula implode(f:(AlleFormula)`some <AlleExpr expr>`, ResolvedDomains dom)
  = nonEmpty(implode(expr,dom), origLoc=f@\loc);
  
translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleExpr lhsExpr> in <AlleExpr rhsExpr>`, ResolvedDomains dom)
  = subset(implode(lhsExpr,dom),implode(rhsExpr,dom), origLoc=f@\loc);
  
translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleExpr lhsExpr> = <AlleExpr rhsExpr>`, ResolvedDomains dom)
  = equal(implode(lhsExpr,dom),implode(rhsExpr,dom), origLoc=f@\loc);
  
translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleExpr lhsExpr> != <AlleExpr rhsExpr>`, ResolvedDomains dom)
  = inequal(implode(lhsExpr,dom),implode(rhsExpr,dom), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleExpr lhsExpr> in <AlleExpr rhsExpr>`, ResolvedDomains dom)
  = subset(implode(lhsExpr,dom),implode(rhsExpr,dom), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleFormula lhsExpr> && <AlleFormula rhsExpr>`, ResolvedDomains dom)
  = conjunction(implode(lhsExpr,dom),implode(rhsExpr,dom), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleFormula lhsExpr> || <AlleFormula rhsExpr>`, ResolvedDomains dom)
  = disjunction(implode(lhsExpr,dom),implode(rhsExpr,dom), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleFormula lhsExpr> =\> <AlleFormula rhsExpr>`, ResolvedDomains dom)
  = implication(implode(lhsExpr,dom),implode(rhsExpr,dom), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleFormula lhsExpr> \<=\> <AlleFormula rhsExpr>`, ResolvedDomains dom)
  = equality(implode(lhsExpr,dom),implode(rhsExpr,dom), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`let <{VarDeclaration ","}+ decls> | <AlleFormula form>`, ResolvedDomains dom)
  = let([implode(d,dom) | d <- decls], implode(form,dom), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`forall <{VarDeclaration ","}+ decls> | <AlleFormula form>`, ResolvedDomains dom)
  = universal([implode(d,dom) | d <- decls], implode(form,dom), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`exists <{VarDeclaration ","}+ decls> | <AlleFormula form>`, ResolvedDomains dom)
  = existential([implode(d,dom) | d <- decls], implode(form,dom), origLoc=f@\loc);

translation::AST::VarDeclaration implode((VarDeclaration)`<RelVar var> : <AlleExpr expr>`, ResolvedDomains dom)
  = varDecl("<var>", implode(expr,dom)); 
  
translation::AST::AlleExpr implode((AlleExpr)`( <AlleExpr expr> )`, ResolvedDomains dom)
  = implode(expr,dom);
  
translation::AST::AlleExpr implode((AlleExpr)`<RelVar v>`, ResolvedDomains dom)
  = relvar("<v>");
 
translation::AST::AlleExpr implode((AlleExpr)`<Literal l>`, ResolvedDomains dom)
  = lit(implode(l,dom));

translation::AST::AlleExpr implode((AlleExpr)`[<{Rename ","}+ rename>] <AlleExpr expr>`, ResolvedDomains dom)
  = rename(implode(expr,dom), [implode(r,dom) | r <- rename]);

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr expr>[<{AttributeName ","}+ atts>]`, ResolvedDomains dom)
  = projection(implode(expr,dom), ["<a>" | a <- atts]);

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr expr> where <Restriction restriction>`, ResolvedDomains dom)
  = restriction(implode(expr,dom), implode(restriction,dom));
  
translation::AST::AlleExpr implode((AlleExpr)`~<AlleExpr expr>`, ResolvedDomains dom)
  = transpose(implode(expr,dom));
translation::AST::AlleExpr implode((AlleExpr)`~<TupleAttributeSelection tas> <AlleExpr expr>`, ResolvedDomains dom)
  = transpose(implode(tas,dom), implode(expr,dom));
    
translation::AST::AlleExpr implode((AlleExpr)`^<AlleExpr expr>`, ResolvedDomains dom)
  = closure(implode(expr,dom));
translation::AST::AlleExpr implode((AlleExpr)`^<TupleAttributeSelection tas> <AlleExpr expr>`, ResolvedDomains dom)
  = closure(implode(tas,dom), implode(expr,dom));

translation::AST::AlleExpr implode((AlleExpr)`*<AlleExpr expr>`, ResolvedDomains dom)
  = reflexClosure(implode(expr,dom));
translation::AST::AlleExpr implode((AlleExpr)`*<TupleAttributeSelection tas> <AlleExpr expr>`, ResolvedDomains dom)
  = reflexClosure(implode(tas,dom), implode(expr,dom));
  
translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs>|x|<AlleExpr rhs>`, ResolvedDomains dom)
  = naturalJoin(implode(lhs,dom), implode(rhs,dom)); 

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs>.<AlleExpr rhs>`, ResolvedDomains dom)
  = dotJoin(implode(lhs,dom), implode(rhs,dom)); 
  
translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> + <AlleExpr rhs>`, ResolvedDomains dom)
  = union(implode(lhs,dom), implode(rhs,dom));

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> & <AlleExpr rhs>`, ResolvedDomains dom)
  = intersection(implode(lhs,dom), implode(rhs,dom));
  
translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> - <AlleExpr rhs>`, ResolvedDomains dom)
  = difference(implode(lhs,dom), implode(rhs,dom));
  
translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> x <AlleExpr rhs>`, ResolvedDomains dom)
  = product(implode(lhs,dom), implode(rhs,dom));
 
translation::AST::TupleAttributeSelection implode ((TupleAttributeSelection)`\<<AttributeName first>,<AttributeName second>\>`, ResolvedDomains dom) 
  = order("<first>","<second>");
  
translation::AST::Rename implode((Rename)`<AttributeName new> / <AttributeName orig>`, ResolvedDomains dom) 
  = rename("<new>","<orig>");

translation::AST::Restriction implode((Restriction)`( <Restriction r> )`, ResolvedDomains dom) 
  = implode(r,dom);    

translation::AST::Restriction implode((Restriction)`not <Restriction r>`, ResolvedDomains dom) 
  = not(implode(r,dom));    

translation::AST::Restriction implode((Restriction)`<RestrictionExpr lhs> = <RestrictionExpr rhs>`, ResolvedDomains dom) 
  = equal(implode(lhs, dom),implode(rhs,dom));

translation::AST::Restriction implode((Restriction)`<Restriction lhs> && <Restriction rhs>`, ResolvedDomains dom) 
  = and(implode(lhs, dom),implode(rhs,dom));
  
translation::AST::Restriction implode((Restriction)`<Restriction lhs> || <Restriction rhs>`, ResolvedDomains dom) 
  = or(implode(lhs, dom),implode(rhs,dom));
 
translation::AST::RestrictionExpr implode((RestrictionExpr)`<AttributeName att>`, ResolvedDomains dom) 
  = att("<att>");

translation::AST::RestrictionExpr implode((RestrictionExpr)`<Literal l>`, ResolvedDomains dom) 
  = lit(implode(l,dom));
   
default &T implode(&R production, ResolvedDomains dom) { throw "Unable to implode production \'<production>\'. No implode function implemented"; }
