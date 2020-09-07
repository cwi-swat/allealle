module translation::tests::SymmetryBreakerTester

import ide::Parser;
import translation::Imploder;
import translation::AST;
import translation::Environment;

import smtlogic::Core;

import translation::SymmetryBreaker;

Formula breakPigeonHoleSymmetries() = findSymmetryPredicates(loadProblem(ph()));
Formula breakFileSystemSymmetries() = findSymmetryPredicates(loadProblem(fs()));

str ph() = "Pigeon (pId:id)            = {\<p1\>..\<p10\>}
           'Hole   (hId:id)            = {\<h1\>..\<h9\>}
           'nest   (pId:id, hId:id)   \<= {\<p1,h1\>..\<p10,h9\>}
           '
           'nest ⊆ Pigeon ⨯ Hole
           '∀ p ∈ Pigeon | one   p ⨝ nest
           '∀ h ∈ Hole | lone  h ⨝ nest";

str fs() = "File (id:id)             \<= {\<f0\>..\<f2\>}
           'Dir (id:id)              \<= {\<d0\>,\<d1\>}
           'Root (id:id)              = {\<d0\>}
           'contents (from:id,to:id) \>= {\<d0,d1\>} \<= {\<d0,d0\>..\<d1,d1\>,\<d0,f0\>..\<d1,f2\>}
           '           
           'contents ⊆ Dir[id as from] ⨯ (Dir ∪ File)[id as to]
           '∀ d ∈ Dir | ¬ (d[id as to] ⊆ (d[id as from] ⨝ ^\<from,to\>contents)[to])
           'Root ⊆ Dir
           '(File ∪ Dir)[id as to] ⊆ (Root[id as from] ⨝ *\<from,to\>contents)[to]
           '∀ f ∈ (File ∪ Dir) | lone contents ⨝ f[id as to]";

Problem loadProblem(str prob) = implodeProblem(parseString(prob).top);

Formula findSymmetryPredicates(Problem p) {
  sbp = buildSymmetryBreakingPredicates(p, createInitialEnvironment(p));
  
  return sbp;
}


