module translation::SMTInterface

import translation::AST;
import translation::Relation;
import translation::Environment;
import translation::SMTValueSyntax;

extend translation::theories::integer::SMTInterface;
extend translation::theories::string::SMTInterface;

import smtlogic::Core;

import util::Maybe;  
import String;
import IO;
import List;
import Map;
import ParseTree;

alias SMTVar = tuple[str name, Sort sort];
alias SMTModel = map[SMTVar, Term];

data ModelAttribute
  = idAttribute(str name, str id)
  | fixedAttribute(str name, Term val)
  | varAttribute(str name, Term val, str smtVarName)
  ;
  
data ModelTuple
  = fixedTuple(list[ModelAttribute] attributes)
  | varTuple(list[ModelAttribute] attributes, str smtVarName)
  ;  

data ModelRelation 
  = mRelation(str name, Heading heading, list[ModelTuple] tuples)
  ;
    
data Model 
  = model(set[ModelRelation] relations)
  | empty()
  ;

set[SMTVar] collectSMTVars(Environment env)  {
  set[SMTVar] result = {<var, env.createdVars()[var]> | str var <- env.createdVars()};
  
  for (str varName <- env.relations, Relation r := env.relations[varName], Tuple t <- r.rows) {
    result += {<name, sort> | /var(str name, Sort sort) := t};
    
    if (pvar(str name) := r.rows[t].exists) {
      result += <name, \bool()>;
    }
  }    
    
  return result;
}

set[Sort] collectSorts(set[SMTVar] vars) = {v.sort | SMTVar v <- vars}; 

str preambles(set[SMTVar] vars) = "<for (s <- collectSorts(vars)) {><preamble(s)>
                                  '<}>";

default str preamble(Sort srt) = "";

str compileSMTVariableDeclarations(set[SMTVar] vars) = "<for (SMTVar var <- vars) {>
                                                       '<compileVariableDeclaration(var)><}>";

str compileVariableDeclaration(<str name, Sort::\bool()>) = "(declare-const <name> Bool)";
default str compileVariableDeclaration(SMTVar var) { throw "Unable to compile variable <var> to SMT, no SMT compiler available for sort \'<var.sort>\'"; }

@memo
str compile(\and(set[Formula] forms))         = "(and <for (f <- forms) {>
                                                '  <compile(f)><}>
                                                ')";
@memo
str compile(\or(set[Formula] forms))          = "(or <for (f <- forms) {>
                                                '  <compile(f)><}>
                                                ')";

@memo str compile(\not(Formula f))                  = "(not <compile(f)>)"; 
@memo str compile(ite(Formula c, Term t, Term e))   = "(ite " + compile(c) + " " + compile(t) + " " + compile(e) + ")\n";
@memo str compile(\false())                         = "false"; 
@memo str compile(\true())                          = "true";
@memo str compile(\pvar(name))                      = name; 
@memo str compile(equal(set[Formula] fs))           = "(= <for (Formula f <- fs) {> <compile(f)><}>)"; 
@memo str compile(equal(set[Term] ts))              = "(= <for (Term t <- ts) {> <compile(t)><}>)";

default str compile(Formula f)                { throw "Unable to compile Formula <f> to SMT, no SMT compile function available"; }

@memo str compile(lit(Literal l))                   = compile(l);
@memo str compile(var(str name, Sort s))            = name;

@memo str compile(ttrue())                          = "true";
@memo str compile(ffalse())                         = "false";
@memo str compile(id(str i))                        { throw "Unable to compile id \'<i>\' to SMT"; }

@memo str compile(aggregateFunc(str name, Formula exists, Term t, Term accum)) = "(<name> <compile(exists)> <compile(t)> <compile(accum)>)";
@memo str compile(aggregateFunc(str name, Formula exists, Term accum)) = "(<name> <compile(exists)> <compile(accum)>)";

default str compile(Term t)                   { throw "Unable to compile Term <t> to SMT, no SMT compile function available"; }

@memo
str compileWithoutIden(\and(set[Formula] forms)) {
   str clauses = "";
   for (f <- forms) {
    clauses += compileWithoutIden(f) + " ";
   }
   
   return "(and " + clauses + ")\n";
}   

@memo
str compileWithoutIden(\or(set[Formula] forms))  { 
   str clauses = "";
   for (f <- forms) {
    clauses += compileWithoutIden(f) + " ";
   }
   
   return "(or " + clauses + ")\n";
}

@memo
str compileWithoutIden(\not(Formula f))                  = "(not " + compileWithoutIden(f) + ")"; 
@memo
str compileWithoutIden(ite(Formula c, Term t, Term e))   = "(ite " + compileWithoutIden(c) + " " + compileWithoutIden(t) + " " + compileWithoutIden(e) + ")\n";
@memo
str compileWithoutIden(\false())                         = "false"; 
@memo
str compileWithoutIden(\true())                          = "true";
@memo
str compileWithoutIden(\pvar(name))                      = name; 

@memo
str compileWithoutIden(equal(set[Formula] fs)) { 
   str clauses = "";
   for (f <- fs) {
    clauses += compileWithoutIden(f) + " ";
   }
   
  return "(= " + clauses + ")";
}

@memo
str compileWithoutIden(equal(set[Term] ts)) {
   str clauses = "";
   for (t <- ts) {
    clauses += compileWithoutIden(t) + " ";
   }
   
  return "(= " + clauses + ")";
}

@memo
str compileWithoutIden(lit(Literal l))                   = compileWithoutIden(l);
@memo
str compileWithoutIden(var(str name, Sort s))            = name;
@memo
str compileWithoutIden(ttrue())                          = "true";
@memo
str compileWithoutIden(ffalse())                         = "false";
@memo
str compileWithoutIden(id(str i))                        { throw "Unable to compileWithoutIden id \'<i>\' to SMT"; }
@memo
str compileWithoutIden(aggregateFunc(str name, Formula exists, Term t, Term accum)) = "(" + name + " " + compileWithoutIden(exists) + " " + compileWithoutIden(t) + " " + compileWithoutIden(accum) + ")";
@memo
str compileWithoutIden(aggregateFunc(str name, Formula exists, Term accum)) = "(" + name + " " + compileWithoutIden(exists) + " " + compileWithoutIden(accum) + ")";

default str compileWithoutIden(Formula f) { throw "Unable to compileWithIden <f> to SMT, no SMT compileWithIdenr available"; }

str compileAssert(Formula f, bool prettyPrint = false) {
  if (!prettyPrint) {
    return "\n(assert " + compileWithoutIden(f) + ")";
  } else {
    return "\n(assert 
           '  <compile(f)>
           ')";
  }
} 
                                 
str compileCommands(list[Command] commands) {
  str smt = "";
  //if (commands != []) {
  //  smt += "(set-option :opt.priority box)\n";
  //}  
  for (Command c <- commands) {
    smt += "<compileCommand(c)>\n";
  }
  
  return smt;
}                               

str compileCommand(setOption(Option op)) = "(set-option <compile(op)>)";
str compileCommand(minimize(Term t)) = "(minimize <compile(t)>)";
str compileCommand(maximize(Term t)) = "(maximize <compile(t)>)";

str compile(optimizationPriority(OptPriority prio)) = ":opt.priority <compile(prio)>";

str compile(lexicographic()) = "lex";
str compile(pareto()) = "pareto";
str compile(independent()) = "box";

default str compileCommand(Command c) { throw "Unable to compile command \'<c>\'. No compile function defined.";}

SMTModel getValues(str smtResult, set[SMTVar] vars) {
  SmtValues foundValues;
  try {
    foundValues = parse(#start[SmtValues], trim(smtResult)).top;
  } catch: {
    writeFile(|project://allealle/bin/errorResponse.resp|, smtResult);
    throw "Unable to parse found result by SMT solver. Saved found result to file";
  }
   
  map[str,SmtValue] rawSmtVals = (() | it + ("<varAndVal.name>":varAndVal.val) | VarAndValue varAndVal <- foundValues.values);

  SMTModel m = (var : val | str varName <- rawSmtVals, SMTVar var:<varName, Sort _> <- vars, Term val := getValue(rawSmtVals[varName], var));
  
  return m;
}    

Term getValue((SmtValue)`true`, <str _, Sort::\bool()>) = lit(ttrue());
Term getValue((SmtValue)`false`, <str _, Sort::\bool()>) = lit(ffalse());
default Term getValue(SmtValue smtValue, SMTVar var) { throw "Unable to get the value for SMT value `<smtValue>`, for variable `<var>`"; }

str negateVariable(str var, lit(ttrue())) = "(not <var>)";
str negateVariable(str var, lit(ffalse())) = var;

default str negateVariable(str v, Term t) { throw "Unable to negate variable <v> with current value <t>"; }

Model constructRelationalModel(SMTModel smtModel, Environment env) { 
  list[ModelAttribute] constructAttributes(Tuple t) {
    list[ModelAttribute] attributes = [];
    for (str att <- t) {
      if (lit(id(str k)) := t[att]) {
        attributes += idAttribute(att,k);
      } else if (l:lit(Literal _) := t[att]) {
        attributes += fixedAttribute(att, l); 
      } else if (v:var(str name, Sort s) := t[att]) {
        attributes += varAttribute(att, smtModel[<name,s>], name);
      }
    } 
     
    return attributes; 
  }
  
  set[ModelRelation] relations = {};
  
  for (str relName <- env.relations) {
    list[ModelTuple] tuples = [];
    Relation r = env.relations[relName];
     
    for (Tuple t <- r.rows) {
      if (r.rows[t].exists == \true()) {
        tuples += fixedTuple(constructAttributes(t));
      } else if (pvar(str name) := r.rows[t].exists && smtModel[<name,\bool()>] == lit(ttrue())) {
        tuples += varTuple(constructAttributes(t), name);
      }
    }
    
    relations += mRelation(relName, env.relations[relName].heading, tuples);
  }
  
  return model(relations);
} 