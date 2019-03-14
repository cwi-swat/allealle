module translation::Imploder

import translation::Syntax;
import translation::AST;

import ParseTree;
import String;
import util::Maybe;

translation::AST::Problem implodeProblem(translation::Syntax::Problem p) {
  Maybe[translation::AST::ObjectiveSection] s = (/translation::Syntax::ObjectiveSection objSec := p.objSection) ? just(implode(objSec)) : nothing();
  Maybe[translation::AST::Expect] e = (/translation::Syntax::Expect exp := p.expect) ? just(implode(exp)) : nothing();
     
  return problem([implode(r) | r <- p.relations], [implode(c) | c <- p.constraints], s, e);
}
//translation::AST::Problem implodeProblem(translation::Syntax::Problem p) 
//  = problem([implode(r) | r <- p.relations], [implode(c) | c <- p.constraints], implode(objSec)) //[implode(obj) | obj <- objSec.objectives])
//  when /translation::Syntax::ObjectiveSection objSec := p.objSection; 

translation::AST::RelationDef implode((Relation)`<RelVar v> (<{HeaderAttribute ","}+ header>) <RelationalBound bounds>`) 
  = relation("<v>", [implode(h) | h <- header], implode(bounds));
 
translation::AST::HeaderAttribute implode((HeaderAttribute)`<AttributeName name> : <Domain d>`)
  = header("<name>", implode(d));

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
  = idd("<i>");   

translation::AST::AlleValue implode((Value)`<Literal l>`)
  = alleLit(implode(l));  
 
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

translation::AST::AlleLiteral implode((Literal)`'<Idd id>'`)
  = idLit(id);

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

translation::AST::AlleFormula implode(f:(AlleFormula)`<AlleExpr expr>::[<Criteria crit>]`)
  = \filter(implode(expr), implode(crit));

translation::AST::AlleFormula implode(f:(AlleFormula)`let <{VarBinding ","}+ bindings> | <AlleFormula form>`)
  = let([implode(b) | b <- bindings], implode(form), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`∀ <{VarDeclaration ","}+ decls> | <AlleFormula form>`)
  = universal([implode(d) | d <- decls], implode(form), origLoc=f@\loc);

translation::AST::AlleFormula implode(f:(AlleFormula)`∃ <{VarDeclaration ","}+ decls> | <AlleFormula form>`)
  = existential([implode(d) | d <- decls], implode(form), origLoc=f@\loc);

translation::AST::VarDeclaration implode((VarDeclaration)`<RelVar var> ∈ <AlleExpr expr>`)
  = varDecl("<var>", implode(expr)); 

translation::AST::VarBinding implode((VarBinding)`<RelVar var> = <AlleExpr expr>`)
  = varBinding("<var>", implode(expr)); 
  
translation::AST::AlleExpr implode((AlleExpr)`( <AlleExpr expr> )`)
  = implode(expr);
  
translation::AST::AlleExpr implode((AlleExpr)`<RelVar v>`)
  = relvar("<v>");
 
translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr expr>[<{Rename ","}+ ren>]`)
  = rename(implode(expr), [implode(r) | r <- ren]);

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr expr>[<{ProjectAndRename ","}+ rp>]`)
  = rename(project(implode(expr), [implodeProject(r) | r <- rp]), [implode(r) | r <- rp]);

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr expr>[<{AttributeName ","}+ atts>]`)
  = project(implode(expr), ["<a>" | a <- atts]);

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr expr>[<{AggregateFunctionDef ","}+ funcs>]`)
  = aggregate(implode(expr), [implode(f) | f <- funcs]);

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr expr>[<{AttributeName ","}+ groupBy>,<{AggregateFunctionDef ","}+ funcs>]`)
  = groupedAggregate(implode(expr), ["<n>" | AttributeName n <- groupBy], [implode(f) | f <- funcs]);

translation::AST::AlleExpr implode((AlleExpr)`<AlleExpr expr> where <Criteria criteria>`)
  = select(implode(expr), implode(criteria));
  
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
  
translation::AST::Rename implode((Rename)`<AttributeName orig> as <AttributeName new>`) 
  = rename("<new>","<orig>");

translation::AST::Rename implode((ProjectAndRename)`<AttributeName orig> -\> <AttributeName new>`) 
  = rename("<new>","<orig>");
  
str implodeProject((ProjectAndRename)`<AttributeName orig> -\> <AttributeName new>`)
  = "<orig>";

translation::AST::AggregateFunctionDef implode((AggregateFunctionDef)`<AggregateFunction func>`)
  = aggFuncDef(implode(func), "<replaceAll(replaceAll("<func>","(","_"),")","")>");

translation::AST::AggregateFunctionDef implode((AggregateFunctionDef)`<AggregateFunction func> as <AttributeName bindTo>`)
  = aggFuncDef(implode(func), "<bindTo>");

translation::AST::Criteria implode((Criteria)`( <Criteria cr> )`) 
  = implode(cr);    
 
translation::AST::Criteria implode((Criteria)`not <Criteria r>`) 
  = not(implode(r));    

translation::AST::Criteria implode((Criteria)`<CriteriaExpr lhs> = <CriteriaExpr rhs>`) 
  = equal(implode(lhs),implode(rhs));

translation::AST::Criteria implode((Criteria)`<CriteriaExpr lhs> != <CriteriaExpr rhs>`) 
  = inequal(implode(lhs),implode(rhs));

translation::AST::Criteria implode((Criteria)`<Criteria lhs> && <Criteria rhs>`) 
  = and(implode(lhs),implode(rhs));
  
translation::AST::Criteria implode((Criteria)`<Criteria lhs> || <Criteria rhs>`) 
  = or(implode(lhs),implode(rhs));

translation::AST::CriteriaExpr implode((CriteriaExpr)`(<CriteriaExpr expr>)`) 
  = implode(expr);
 
translation::AST::CriteriaExpr implode((CriteriaExpr)`<AttributeName at>`) 
  = att("<at>");

translation::AST::CriteriaExpr implode((CriteriaExpr)`<Literal l>`) 
  = litt(implode(l));

translation::AST::CriteriaExpr implode((CriteriaExpr)`<Criteria condition> ? <CriteriaExpr thn> : <CriteriaExpr els>`) 
  = ite(implode(condition),implode(thn),implode(els));

translation::AST::ObjectiveSection implode((ObjectiveSection)`objectives: <{Objective ","}+ objs>`) 
  = objectives(lex(), [implode(obj) | obj <- objs]);  

translation::AST::ObjectiveSection implode((ObjectiveSection)`objectives (<ObjectivePriority prio>): <{Objective ","}+ objs>`) 
  = objectives(implode(prio),[implode(obj) | obj <- objs]);  

translation::AST::ObjectivePriority implode((ObjectivePriority)`lex`) = lex();
translation::AST::ObjectivePriority implode((ObjectivePriority)`pareto`) = pareto();
translation::AST::ObjectivePriority implode((ObjectivePriority)`independent`) = independent();

translation::AST::Objective implode((Objective)`maximize <AlleExpr expr>`)
  = maximize(implode(expr));

translation::AST::Objective implode((Objective)`minimize <AlleExpr expr>`)
  = minimize(implode(expr));

translation::AST::Expect implode((Expect)`expect: <ResultType result>`)
  = expect(implode(result));

translation::AST::Expect implode((Expect)`expect: <ResultType result>, <ModelRestriction models>`)
  = expect(implode(result), implode(models));
  
translation::AST::ResultType implode((ResultType)`sat`) = sat();
translation::AST::ResultType implode((ResultType)`trivial-sat`) = trivSat();
translation::AST::ResultType implode((ResultType)`unsat`) = unsat();
translation::AST::ResultType implode((ResultType)`trivial-unsat`) = sat();
   
translation::AST::ModelRestriction implode((ModelRestriction)`#models <ModelRestrExpr expr>`)
  = restrict(implode(expr), id());   

translation::AST::ModelRestriction implode((ModelRestriction)`#models (<Domain d>) <ModelRestrExpr expr>`)
  = restrict(implode(expr), implode(d));   

translation::AST::ModelRestrExpr implode((ModelRestrExpr)`= <Arity nr>`) = eqMod(toInt("<nr>"));
translation::AST::ModelRestrExpr implode((ModelRestrExpr)`\< <Arity nr>`) = ltMod(toInt("<nr>"));
translation::AST::ModelRestrExpr implode((ModelRestrExpr)`\> <Arity nr>`) = gtMod(toInt("<nr>"));
   
default &T implode(&R production) { throw "Unable to implode production \'<production>\'. No implode function implemented"; }
