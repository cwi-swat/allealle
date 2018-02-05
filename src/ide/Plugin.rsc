module ide::Plugin

import ide::Parser;
import ide::CombinedSyntax;
import ide::CombinedAST;
import ide::CombinedImploder;
import ide::CombinedModelFinder;
import ide::vis::ModelVisualizer;
import ide::UnicodeRewriter;
import ide::UnionCompatibilityChecker;

import translation::Translator;
import translation::SMTInterface;

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
	ide::CombinedSyntax::Problem cachedProblem = [ide::CombinedSyntax::Problem]""; 
	
	UnionCompatibilityResult getLatestCompatibilityResult(ide::CombinedSyntax::Problem p) {
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
			action("Check and visualize", (Tree current, loc file) {
				if (/ide::CombinedSyntax::Problem p := current) {checkAndVisualize(p);}
			})
		),
		syntaxProperties(#start[Problem]),
		liveUpdater(unicodeRewrite),
		builder(set[Message] ((&T<:Tree) current) {
		  if (/ide::CombinedSyntax::Problem p := current) {
		    UnionCompatibilityResult r = getLatestCompatibilityResult(p);
		    return r.messages;
		  } 
		}),
		annotator((&T<:Tree) (&T<:Tree current) {
      if (/ide::CombinedSyntax::Problem p := current) {
        UnionCompatibilityResult r = getLatestCompatibilityResult(p);
        
        return current[@docs = (l : getHover(r.headings[l]) | l <- r.headings)];
      }  
		})
	};
	
	registerContributions(lang, contribs);
} 
 
void checkAndVisualize(ide::CombinedSyntax::Problem p) {  
	ModelFinderResult result = checkInitialSolution(implodeProblem(p)); 
	if (sat(Model currentModel, Model (ide::CombinedAST::Domain) nextModel, void () stop) := result) {
		renderModel(currentModel, nextModel, stop);
	} else if (trivialSat(Model model) := result) {
	  renderModel(model, Model (ide::CombinedAST::Domain) { return empty(); }, void () {;});
	} else if (trivialUnsat() := result) {
    alert("Not satisfiable (trivially), nothing to visualize");
	} else {
		alert("Not satisfiable (smt solver can not find a model), nothing to visualize");
	}
}