module tests::IntegrationTests

import ide::CombinedModelFinder;
import ide::Imploder;
import ide::CombinedAST;

private ModelFinderResult \solve(loc problem) = checkInitialSolution(implodeProblem(problem));

private ModelFinderResult shouldBeSat(loc problem) = s when s:sat(Model _, Universe _, Model (Theory) _, void () _) := \solve(problem); 
private default ModelFinderResult shouldBeSat(loc _) { throw "Problem \'<problem>\' should be satisfiable but is not";}

private ModelFinderResult shouldBeTrivialSat(loc problem) = s when s:trivialSat(Model _, Universe _) := \solve(problem);
private default ModelFinderResult shouldBeTrivialSat(loc _) { throw "Problem \'<problem>\' should be trivially satisfiable but is not";}


private ModelFinderResult shouldBeUnsat(loc problem) = u when u:unsat(set[Formula] _) := \solve(problem);
private default ModelFinderResult shouldBeUnsat(loc _) {throw "Problem \'<problem>\' should be unsatisfiable but is";}

private ModelFinderResult shouldBeTrivialUnsat(loc problem) = u when u:trivialUnsat() := \solve(problem);
private default ModelFinderResult shouldBeTrivialUnsat(loc _) {throw "Problem \'<problem>\' should be unsatisfiable but is";}

test bool additionOfFixedRelationsResultInFixedAddedRelations() {
  try {
    ModelFinderResult r = shouldBeSat(|project://allealle/tests/additionOfTwoFixedRelationsAlwaysLeadsToAFixedTenaryAdditionRelation.alle|);
    Model next = r.nextModel(intTheory());
    r.stop();
    
    return empty() := next;
  } catch ex: fail;
}

test bool additionOfComposedAndJoinedFixedRelationsResultInFixedAddedRelations() {
  try {
    ModelFinderResult r = shouldBeSat(|project://allealle/tests/additionOfTwoComposedAndJoinedFixedRelationsShouldResultInAFixedAddedRelation.alle|);
    Model next = r.nextModel(intTheory());
    r.stop();
    
    return empty() := next;
  } catch ex: fail;
}

test bool additionIsCommutative() {
  try {
    ModelFinderResult r = shouldBeSat(|project://allealle/tests/additionIsCommutative.alle|);
    Model next = r.nextModel(intTheory());
    r.stop();
    
    return empty() := next;
  } catch ex: fail;
  
}
