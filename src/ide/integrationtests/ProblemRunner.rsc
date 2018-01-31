module ide::integrationtests::ProblemRunner

import ide::CombinedImploder;
import ide::CombinedAST;
import ide::CombinedModelFinder;

import translation::SMTInterface;

import smtlogic::Core;
  
import IO;
import List;
import Set;
import String;

tuple[void () next, void (Domain) nextWithDom, void () stop] translateAndSolve(loc problem) {
  Problem p = implodeProblem(problem);
  
  Model m = empty();
  
  ModelFinderResult r = checkInitialSolution(p);
  if (sat(Model model, Model (Domain) nextModel, void () stop) := r) {
    m = model;
    
    void next() = nextWithDom(id());
    
    void nextWithDom(Domain d) {  
      model = nextModel(d);
      printModel(model);
  
      if (model == empty()) { stop(); }
    } 
  
    printModel(model);
    
    return <next, nextWithDom, stop>;
  } 
  else if (trivialSat(Model model) := r) {
    println("Trivially satisfiable");
  }
  else if (unsat(set[Formula] _) := r) {
    println("Unsatisfiable");
  }
  else if (trivialUnsat() := r) {
    println("Trivially unsatisfiable");
  }
  
}

void printModel(empty()) { println("no more models"); }

void printModel(Model model) {
  int pad = 8;

  str printAttribute(idAttribute(str name, str id)) = " <left("<id>", pad-2)> ";
  str printAttribute(fixedAttribute(str name, Term val)) = " <left("<printTerm(val)> (*)", pad-2)> ";
  str printAttribute(varAttribute(str name, Term val, str smtVarName)) = " <left("<printTerm(val)>", pad-2)> ";

  str printTuple(fixedTuple(set[ModelAttribute] attributes), list[str] heading) = "<intercalate("|", [printAttribute(at) | str h <- heading, ModelAttribute at <- attributes, at.name == h])> (+)"; 
  str printTuple(varTuple(set[ModelAttribute] attributes, str name), list[str] heading) = intercalate("|", [printAttribute(at) | str h <- heading, ModelAttribute at <- attributes, at.name == h]);

  str printHeading(list[str] heading) = "<intercalate("|", [" <left(h, pad-2)> " | h <- heading])>";

  println("-----------"); 

  if (model.relations == {}) {
    println("No visible relations");
  } else {
    for (ModelRelation r <- model.relations) {
      list[str] heading = [h | str h <- r.heading];
      println("<r.name>:");
      println(printHeading(heading));
      println(left("", size(heading) * pad + size(heading), "="));
      
      for (ModelTuple t <- r.tuples) {
        println(printTuple(t, heading));
      } 
      
      println("");
    }
  }
  
  println("-----------");
}