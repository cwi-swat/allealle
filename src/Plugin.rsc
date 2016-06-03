module Plugin

import extended::Parser;
import extended::Syntax;
import extended::AST;
import extended::Imploder;
import extended::Translator; 
import extended::ModelFinder;

import vis::ModelVisualizer;

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
				if (/extended::Syntax::Problem p := current) {checkAndVisualize(p);}
			})
		)
	};
	
	registerContributions(lang, contribs);
}

void checkAndVisualize(extended::Syntax::Problem p) {
	ModelFinderResult result = checkInitialSolution(implodeProblem(p));

	if (sat(Environment currentModel, extended::AST::Universe uni, Environment () nextModel, void () stop) := result) {
		renderModel(uni, currentModel, nextModel, stop);
	} else {
		alert("Not satisfiable, can not visualize");
	}
}