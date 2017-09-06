module ide::integrationtests::ProblemRunner

import ide::Imploder;
import ide::CombinedAST;
import ide::CombinedModelFinder;

import translation::SMTInterface;
  
import IO;
import List;
import Set;

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
  str printValue(lit(posInt(int i))) ="<i>";
  str printValue(lit(negInt(int i))) = "< -i>";

  str printAttribute(ModelAttribute at) = "<at.name>:<printValue(at.val)>";

  str printTuple(ModelTuple t) = "\<<intercalate(",", [id | Id id <- t.idx.idx])>\>" when t.attributes == []; 
  str printTuple(ModelTuple t) = "\<<intercalate(",", [id | Id id <- t.idx.idx])>,<intercalate(",", [printAttribute(at) | ModelAttribute at <- t.attributes])>\>" when t.attributes != []; 

  println("-----------"); 

  if (model.relations == {}) {
    println("No visible relations");
  } else {
    for (ModelRelation r <- model.relations) {
      println("<r.name>: {<intercalate(",", [printTuple(t) | ModelTuple t <- r.tuples])>}");
    }
  }
  
  println("-----------");
}