module translation::Imploder

import translation::Syntax;
import translation::AST;
import translation::DomainResolver;

import ParseTree;
import String;

translation::AST::Problem implodeProblem(translation::Syntax::Problem p, ResolvedDomains dom) 
  = problem([implode(r,dom) | r <- p.relations], [implode(c,dom) | c <- p.constraints]); 

translation::AST::Relation implode((Relation)`<Variable v> (<Arity arityOfIds>) <RelationalBound bounds>`, ResolvedDomains dom) 
  = relation("<v>", toInt("<arityOfIds>"), implode(bounds,dom));

translation::AST::Relation implode((Relation)`<Variable v> (<Arity arityOfIds> :: <{AttributeHeader ","}+ header>) <RelationalBound bounds>`, ResolvedDomains dom) 
  = relationWithAttributes("<v>", toInt("<arityOfIds>"), [implode(h,dom) | h <- header], implode(bounds,dom));

translation::AST::AttributeHeader implode((AttributeHeader)`<AttributeName name> : <Domain d>`, ResolvedDomains dom)
  = header("<name>", implode(d, dom));

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

translation::AST::AlleFormula implode((AlleFormula)`not <AlleFormula form>`, ResolvedDomains dom) 
  = negation(implode(form, dom));
  
translation::AST::AlleFormula implode((AlleFormula)`no <AlleExpr expr>`, ResolvedDomains dom)
  = empty(implode(expr,dom))
  when dom[expr@\loc] == ID();
    
translation::AST::AlleFormula implode((AlleFormula)`lone <AlleExpr expr>`, ResolvedDomains dom)
  = atMostOne(implode(expr,dom))
  when dom[expr@\loc] == ID();

translation::AST::AlleFormula implode((AlleFormula)`one <AlleExpr expr>`, ResolvedDomains dom)
  = exactlyOne(implode(expr,dom))
  when dom[expr@\loc] == ID();
  
translation::AST::AlleFormula implode((AlleFormula)`some <AlleExpr expr>`, ResolvedDomains dom)
  = nonEmpty(implode(expr,dom))
  when dom[expr@\loc] == ID();
  
translation::AST::AlleFormula implode((AlleFormula)`<AlleExpr lhsExpr> in <AlleExpr rhsExpr>`, ResolvedDomains dom)
  = subset(implode(lhsExpr,dom),implode(rhsExpr,dom))
  when dom[lhsExpr@\loc] == ID(),
       dom[rhsExpr@\loc] == ID();
  
translation::AST::AlleFormula implode((AlleFormula)`<AlleExpr lhsExpr> = <AlleExpr rhsExpr>`, ResolvedDomains dom)
  = equal(implode(lhsExpr,dom),implode(rhsExpr,dom))
  when dom[lhsExpr@\loc] == ID(),
       dom[rhsExpr@\loc] == ID();
  
translation::AST::AlleFormula implode((AlleFormula)`<AlleExpr lhsExpr> != <AlleExpr rhsExpr>`, ResolvedDomains dom)
  = inequal(implode(lhsExpr,dom),implode(rhsExpr,dom))
  when dom[lhsExpr@\loc] == ID(),
       dom[rhsExpr@\loc] == ID();

translation::AST::AlleFormula implode((AlleFormula)`<AlleExpr lhsExpr> in <AlleExpr rhsExpr>`, ResolvedDomains dom)
  = subset(implode(lhsExpr,dom),implode(rhsExpr,dom))
  when dom[lhsExpr@\loc] == ID(),
       dom[rhsExpr@\loc] == ID();

translation::AST::AlleFormula implode((AlleFormula)`<AlleFormula lhsExpr> && <AlleFormula rhsExpr>`, ResolvedDomains dom)
  = conjunction(implode(lhsExpr,dom),implode(rhsExpr,dom));

translation::AST::AlleFormula implode((AlleFormula)`<AlleFormula lhsExpr> || <AlleFormula rhsExpr>`, ResolvedDomains dom)
  = disjunction(implode(lhsExpr,dom),implode(rhsExpr,dom));

translation::AST::AlleFormula implode((AlleFormula)`<AlleFormula lhsExpr> =\> <AlleFormula rhsExpr>`, ResolvedDomains dom)
  = implication(implode(lhsExpr,dom),implode(rhsExpr,dom));

translation::AST::AlleFormula implode((AlleFormula)`<AlleFormula lhsExpr> \<=\> <AlleFormula rhsExpr>`, ResolvedDomains dom)
  = equality(implode(lhsExpr,dom),implode(rhsExpr,dom));

translation::AST::AlleFormula implode((AlleFormula)`let <{VarDeclaration ","}+ decls> | <AlleFormula form>`, ResolvedDomains dom)
  = let([implode(d,dom) | d <- decls], implode(form,dom));

translation::AST::AlleFormula implode((AlleFormula)`forall <{VarDeclaration ","}+ decls> | <AlleFormula form>`, ResolvedDomains dom)
  = universal([implode(d,dom) | d <- decls], implode(form,dom));

translation::AST::AlleFormula implode((AlleFormula)`exists <{VarDeclaration ","}+ decls> | <AlleFormula form>`, ResolvedDomains dom)
  = existential([implode(d,dom) | d <- decls], implode(form,dom));

translation::AST::VarDeclaration implode((VarDeclaration)`<Variable var> : <AlleExpr expr>`, ResolvedDomains dom)
  = varDecl("<var>", implode(expr,dom))
  when dom[expr@\loc] == ID(); 
  
translation::AST::AlleExpr implode((AlleExpr)`( <AlleExpr expr> )`, ResolvedDomains dom)
  = implode(expr,dom);
  
translation::AST::AlleExpr implode((AlleExpr)`<Variable v>`, ResolvedDomains dom)
  = variable("<v>");

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr expr>::<AttributeName name>`, ResolvedDomains dom)
  = attributeLookup(implode(expr,dom), "<name>");

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs>.<AlleExpr rhs>`, ResolvedDomains dom)
  = \join(implode(lhs,dom), implode(rhs,dom))
  when dom[lhs@\loc] == ID(),
       dom[rhs@\loc] == ID();
  
translation::AST::AlleExpr implode((AlleExpr)`~<AlleExpr expr>`, ResolvedDomains dom)
  = transpose(implode(expr,dom))
  when dom[expr@\loc] == ID();
  
translation::AST::AlleExpr implode((AlleExpr)`^<AlleExpr expr>`, ResolvedDomains dom)
  = closure(implode(expr,dom))
  when dom[expr@\loc] == ID();  

translation::AST::AlleExpr implode((AlleExpr)`*<AlleExpr expr>`, ResolvedDomains dom)
  = reflexClosure(implode(expr,dom))
  when dom[expr@\loc] == ID();
  
translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> + <AlleExpr rhs>`, ResolvedDomains dom)
  = union(implode(lhs,dom), implode(rhs,dom))
  when dom[lhs@\loc] == ID(),
       dom[rhs@\loc] == ID();
       
translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> ++ <AlleExpr rhs>`, ResolvedDomains dom)
  = override(implode(lhs,dom), implode(rhs,dom))
  when dom[lhs@\loc] == ID(),
       dom[rhs@\loc] == ID();       

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> & <AlleExpr rhs>`, ResolvedDomains dom)
  = intersection(implode(lhs,dom), implode(rhs,dom))
  when dom[lhs@\loc] == ID(),
       dom[rhs@\loc] == ID();

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> \\ <AlleExpr rhs>`, ResolvedDomains dom)
  = difference(implode(lhs,dom), implode(rhs,dom))
  when dom[lhs@\loc] == ID(),
       dom[rhs@\loc] == ID();
       
translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr lhs> -\> <AlleExpr rhs>`, ResolvedDomains dom)
  = product(implode(lhs,dom), implode(rhs,dom))
  when dom[lhs@\loc] == ID(),
       dom[rhs@\loc] == ID();

translation::AST::AlleExpr implode((AlleExpr)`<AlleFormula form> ? <AlleExpr then> : <AlleExpr \else>`, ResolvedDomains dom)
  = ifThenElse(implode(form,dom), implode(then,dom), implode(\else,dom))
  when dom[then@\loc] == dom[\else@\loc];              
  
translation::AST::AlleExpr implode((AlleExpr)`{<{VarDeclaration ","}+ decls> | <AlleFormula form> }`, ResolvedDomains dom)
  = comprehension([implode(d,dom) | d <- decls], implode(form,dom));
  
default &T implode(&R production, ResolvedDomains dom) { throw "Unable to implode production \'<production>\'. No implode function implemented"; }
