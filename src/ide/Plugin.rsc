module ide::Plugin

import ide::Parser;
import ide::CombinedSyntax;
import ide::CombinedAST;
import ide::Imploder;
import ide::CombinedModelFinder;
import ide::vis::ModelVisualizer;

import theories::Binder;

import util::IDE;
import util::Prompt;
import IO; 

import ParseTree;
 
void main(){
	str lang = "AlleAlle";

	registerLanguage(lang,"alle", parseFile); 
	
	contribs = {
		popup(
			action("Check and visualize", (Tree current, loc file) {
				if (/ide::CombinedSyntax::Problem p := current) {checkAndVisualize(p);}
			})
		),
		syntaxProperties(#start[Problem])
	};
	
	registerContributions(lang, contribs);
}
 
void checkAndVisualize(ide::CombinedSyntax::Problem p) {
	ModelFinderResult result = checkInitialSolution(implodeProblem(p));

	if (sat(Environment currentModel, ide::CombinedAST::Universe uni, Environment () nextModel, void () stop) := result) {
		renderModel(uni, currentModel, nextModel, stop);
	} else if (trivialSat(Environment model, ide::CombinedAST::Universe uni) := result) {
	  renderModel(uni, model, Environment () { return (); }, void () {;});
	} else if (trivialUnsat() := result) {
    alert("Not satisfiable (trivially), nothing to visualize");
	} else {
		alert("Not satisfiable (smt solver can not find a model), nothing to visualize");
	}
}