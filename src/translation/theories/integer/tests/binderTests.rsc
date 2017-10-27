module translation::theories::integer::tests::binderTests

extend translation::theories::integer::tests::TesterBase;
import translation::AST;

import IO;

test bool additionOfTwoRelationsWithOnlyTruthVals() {
  RelationMatrix a = truths((["a"]:intVar("a"), ["b"]:intVar("b")));
  RelationMatrix b = truths((["c"]:intVar("c"), ["d"]:intVar("d")));

  tuple[RelationMatrix m, list[Formula] additional] result = add([a,b]);
  
  println(result);  
}

test bool additionOfTwoRelationsWithVars() {
  RelationMatrix a = vars((["a"]:intVar("a"), ["b"]:intVar("b")), "A");
  RelationMatrix b = vars((["c"]:intVar("c"), ["d"]:intVar("d")), "B");

  tuple[RelationMatrix m, list[Formula] additional] result = add([a,b]);
  
  println(result);  
}

private tuple[RelationMatrix, list[Formula]] add(list[RelationMatrix] terms) {
  list[Formula] attributeConstraints = [];
  void addAttributeConstraint(Formula constraint) {
    attributeConstraints += constraint;
  }
  
  list[Command] additionalCommands = [];
  void addAdditionalCommand(Command command) {
    additionalCommands += command;  
  }
  
  set[Formula] intermediateVars = {};
  void addIntermediateVar(Formula val) {
    intermediateVars += val;
  }
   
  int tmpNr = 0;  
  Id freshIntermediateId() {
    tmpNr += 1;
    return "_tmp_<tmpNr>";
  }

  RelationMatrix result = nary(terms, Formula (Formula lhs, Formula rhs) { return addition(lhs, rhs); }, \int(0), <addAttributeConstraint,addAdditionalCommand,addIntermediateVar,freshIntermediateId>);
  
  return <result, attributeConstraints>;  
}