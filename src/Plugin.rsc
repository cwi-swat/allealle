module Plugin

import relational::Parser;
import relational::Syntax;
import relational::AST;
import relational::Imploder;

import Translator; 
import ModelFinder;
import Binder;

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
				if (/relational::Syntax::Problem p := current) {checkAndVisualize(p);}
			})
		)
	};
	
	registerContributions(lang, contribs);
}
 
void checkAndVisualize(relational::Syntax::Problem p) {
	ModelFinderResult result = checkInitialSolution(implodeProblem(p));

	if (sat(Environment currentModel, relational::AST::Universe uni, Environment () nextModel, void () stop) := result) {
		renderModel(uni, currentModel, nextModel, stop);
	} else {
		alert("Not satisfiable, can not visualize");
	}
}