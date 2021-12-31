module ide::integrationtests::NQueensChecker

import ModelFinder;
import ide::Imploder;

import translation::AST;
import translation::SMTInterface;

import IO;

void check() {
  Problem p = implodeProblem(|project://allealle/tests/sat/8queens.alle|);
  
  if (sat(Model m, Model (Domain) nextModel, void () stop) := checkInitialSolution(p)) {
    visualizeModel(m);
    stop();
  }
}

void visualizeModel(Model m) {
  map[int,int] board = ();
  
  if (ModelRelation r <- m.relations, r.name == "Queen") {
    for (int nr <- [1..9]) {
      if (ModelTuple t <- r.tuples, idAttribute("qId","q<nr>") <- t.attributes, fixedAttribute("x", lit(\int(int x))) <- t.attributes, varAttribute("y",lit(\int(int y)),_) <- t.attributes) {
        board[x] = y;
      }
    }
  }
  
  println("----------------");
  for (int x <- [1..9]) {
    print("|");
    for (int y <- [1..9]) {
       if (board[x] == y) {
        print("x|");
       }
       else {
        print(" |");  
      }
    }
    print("\n");
    println("-----------------");
  } 
}