module Plugin

import orig::Parser;
import orig::Syntax;
import orig::AST;
import orig::Imploder;
import orig::ModelFinder;
import vis::ModelVisualizer;
import orig::Translator; 

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
				if (/orig::Syntax::Problem p := current) {checkAndVisualize(p);}
			})
		)
	};
	
	registerContributions(lang, contribs);
}

void checkAndVisualize(orig::Syntax::Problem p) {
	ModelFinderResult result = checkInitialSolution(implodeProblem(p));

	if (sat(Environment currentModel, orig::AST::Universe uni, Environment () nextModel, void () stop) := result) {
		renderModel(uni, currentModel, nextModel, stop);
	} else {
		alert("Not satisfiable, can not visualize");
	}
}