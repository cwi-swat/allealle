module ide::integrationtests::ProblemRunner

import theories::Binder;
//import theories::Translator;

import ide::Imploder;
import ide::CombinedAST;
import ide::CombinedModelFinder;
  
import IO;
import List;
import Set;

tuple[void () next, void () stop] translateAndSolve(loc problem) {
  Problem p = implodeProblem(problem);
  
  Model m = empty();
  
  ModelFinderResult r = checkInitialSolution(p);
  if (sat(Model model, Universe universe, Model (Theory) nextModel, void () stop) := r) {
    m = model;
    
    void next() {
      model = nextModel(relTheory());
      printModel(model);
  
      if (model == empty()) { stop(); }
    }  

    printModel(model);
    
    return <next, stop>;
  }  
  else if (trivialSat(Model model, Universe uni) := r) {
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
  str getVectorLabel(list[Atom] vector) = "\<<intercalate(",", [a | Atom a <- vector])>\>";
  
  str getAtomLabel(atomOnly(str name)) = name;
  str getAtomLabel(atomAndTheory(str name, Theory t)) = "<name> (no value. Bug?)";
  str getAtomLabel(atomTheoryAndValue(str name, intTheory(), intVal(int i))) = "<name> (<i>)";

  println("-----------");
  if (size(model.visibleAtoms) == 0) {
    println("No visible atoms");
  } else { 
    println("Visible atoms: <intercalate(", ", [getAtomLabel(ad) | AtomDecl ad <- model.visibleAtoms])>");
  }
  println("");
  bool visibleRel = true;
  
  if (!visibleRel) {
    println("No visible relations");
  } else {
    for (Relation r <- model.relations) {
      println("Relation \'<r.name>\': <intercalate(",", [getVectorLabel(vv.vector) | VectorAndVar vv <- r.relation])>");
    }
  }
  println("-----------");
}