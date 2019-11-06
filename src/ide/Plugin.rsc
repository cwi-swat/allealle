module ide::Plugin

import ide::Parser;
import ide::Imploder;

import translation::Syntax;
import translation::AST;
import translation::Imploder;
import translation::Translator;
import translation::SMTInterface;

import ModelFinder;
import ExpectationRunner;

import ide::vis::ModelVisualizer;
import ide::UnicodeRewriter;
import ide::UnionCompatibilityChecker;

import util::IDE;
import util::Prompt;
import IO; 
import List;

import ParseTree;

anno map[loc,str] Tree@docs;
 
void main(){
	str lang = "AlleAlle";

	registerLanguage(lang,"alle", parseFile); 
	
	UnionCompatibilityResult cachedCompResult = <(),{}>;
	translation::Syntax::Problem cachedProblem = [translation::Syntax::Problem]""; 
	
	UnionCompatibilityResult getLatestCompatibilityResult(translation::Syntax::Problem p) {
    if (p == cachedProblem) {
      return cachedCompResult;
    } else {
      return checkUnionCompatibilty(p);
    }
  } 
  
  str getHover(heading(map[str,str] attributes)) = "<intercalate(", ", ["<a> : <attributes[a]>" | str a <- attributes])>";
  str getHover(incompatible()) = "?";
	
	contribs = {
		popup(
		  group("AlleAlle", [
  			action("Check and visualize", (Tree current, loc file) {
	 		  	if (/translation::Syntax::Problem p := current) {checkAndVisualize(p);}
	   		}),
	   		action("Check expectation", (Tree current, loc file) {
   		    if (/translation::Syntax::Problem p := current) {
   		      ExpectationResult r = checkExpectation(implodeProblem(p));
   		      if (success() := r) {
   		        alert("Success!");
   		      } else if (failed(str reason) := r) {
   		        alert("Failed! <reason>");
   		      }
   		    }
   		  })]
	   )
		),
		syntaxProperties(#start[Problem]),
		liveUpdater(unicodeRewrite),
		builder(set[Message] ((&T<:Tree) current) {
		  if (/translation::Syntax::Problem p := current) {
		    UnionCompatibilityResult r = getLatestCompatibilityResult(p);
		    return r.messages;
		  } 
		}),
		annotator((&T<:Tree) (&T<:Tree current) {
      if (/translation::Syntax::Problem p := current) {
        UnionCompatibilityResult r = getLatestCompatibilityResult(p);
        
        return current[@docs = (l : getHover(r.headings[l]) | l <- r.headings)];
      }  
		})
	};
	
	registerContributions(lang, contribs);
} 
 
void checkAndVisualize(translation::Syntax::Problem p) {  
	ModelFinderResult result = checkInitialSolution(implodeProblem(p)); 
	if (sat(Model currentModel, Model (translation::AST::Domain) nextModel, void () stop) := result) {
		renderModel(currentModel, nextModel, stop);
	} else if (trivialSat(Model model) := result) {
	  renderModel(model, Model (translation::AST::Domain) { return empty(); }, void () {;});
	} else if (trivialUnsat() := result) {
    alert("Not satisfiable (trivially), nothing to visualize");
	} else {
		alert("Not satisfiable (smt solver can not find a model), nothing to visualize");
	}
}