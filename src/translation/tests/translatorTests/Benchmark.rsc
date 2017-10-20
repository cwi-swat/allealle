module translation::tests::translatorTests::Benchmark

//import translation::tests::binderTests::TesterBase;
import translation::tests::binderTests::Benchmark;
import translation::Binder;
import translation::Translator;
import translation::AST;
import translation::Unparser;

import logic::Propositional;

import IO;
import util::Maybe;
import util::Benchmark;

Environment buildEnvironment(map[str, SimpleRelationMatrix] simpleEnv) 
  = <(relName : convert(simpleEnv[relName], uni) | str relName <- simpleEnv),()> when uni := constructUniverse([simpleEnv[n] | n <- simpleEnv]);

Environment ext(Environment orig, RelationMatrix newVar, str varName) = <orig.relations + (varName:newVar), orig.attributes>;

void runCompleteProblem() {
  list[int] times = runBenchmark(conjunction(conjunction(nestSubsetOfPigeonTimesHole(), forallPigeonsOneHole()), forallHolesSomePigeon()), 50, 50, 10, 20);
  println(times);
}

AlleFormula nestSubsetOfPigeonTimesHole() = subset(variable("nest"), product(variable("Pigeon"), variable("Hole")));
AlleFormula forallPigeonsOneHole() = universal([varDecl("p", variable("Pigeon"))], exactlyOne(\join(variable("p"), variable("nest"))));
AlleFormula forallHolesSomePigeon() = universal([varDecl("h", variable("Hole"))], nonEmpty(\join(variable("nest"), variable("h"))));

list[int] runBenchmark(AlleFormula f, int nrOfPigeons, int nrOfHoles, int warmup, int rounds) {
  println("Preparing \'<unparse(f)>\' formula translation benchmark for <nrOfPigeons> pigeons and <nrOfHoles> holes");
    
  pigeons = constructPigeonRelation(nrOfPigeons);
  holes = constructPigeonRelation(nrOfHoles);
  
  Environment env = buildEnvironment(("Pigeon":pigeons, "Hole":holes, "nest":constructNestRelation(pigeons, holes)));
  
  FormulaCache formCache = ();
  ExprCache exprCache = ();
  
  Maybe[Formula] formulaLookup(FormulaCacheKey key) = just(formCache[key]) when key in formCache;
  default Maybe[Formula] formulaLookup(FormulaCacheKey key) = nothing();
  void storeFormula(FormulaCacheKey key, Formula f) { formCache[key] = f; }
  
  Maybe[RelationMatrix] exprLookup(ExprCacheKey key) = just(exprCache[key]) when key in exprCache;
  default Maybe[RelationMatrix] exprLookup(ExprCacheKey key) = nothing();
  void storeExpr(ExprCacheKey key, RelationMatrix rm) { exprCache[key] = rm; }
  
  void clearCache() {
    formCache = ();
    exprCache = ();
  }
  
  set[Formula] attributeConstraints = {};
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

  print("Warming up (<warmup> rounds): ");
  for (int i <- [0..warmup]) {
    clearCache();
    r = translateCachedFormula(f, env, <addAttributeConstraint, addAdditionalCommand, addIntermediateVar, freshIntermediateId>, cache(formulaLookup, storeFormula, exprLookup, storeExpr));
    print(".");
  }
  print("done\n");
  
  list[int] times = [];
  
  Formula r;
  
  print("Running benchmark (<rounds> total iterations): ");
  for (int i <- [0..rounds]) {
    clearCache();
        
    int startTime = cpuTime();
    r = translateCachedFormula(f, env, <addAttributeConstraint, addAdditionalCommand, addIntermediateVar, freshIntermediateId>, cache(formulaLookup, storeFormula, exprLookup, storeExpr));
    times += [(cpuTime() - startTime) / 1000000];

    print(".");
  }
  
  print("done\n");

  return times;
}