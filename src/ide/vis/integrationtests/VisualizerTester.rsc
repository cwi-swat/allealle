module ide::vis::integrationtests::VisualizerTester

import ModelFinder;
import theories::Binder; 

import ide::CombinedAST;
import ide::CombinedModelFinder;
import ide::Imploder;
import ide::vis::ModelVisualizer; 

import IO; 

void testPigeonHoleProblem() {
	str problem = 	"{h1, h2, p1, p2, p3} 
					'Pigeon:1	[{}, {\<p1\>,\<p2\>,\<p3\>}]
					'Hole:1		[{}, {\<h1\>,\<h2\>}]
					'nest:2		[{}, {\<p1,h1\>,\<p1,h2\>,\<p2,h1\>,\<p2,h2\>,\<p3,h1\>,\<p3,h2\>}]
					'nest in Pigeon -\> Hole
					'forall p:Pigeon | one p.nest
					'forall h:Hole | lone nest.h";
	 
	Problem p = implodeProblem(problem);
	ModelFinderResult result = checkInitialSolution(p);
	
	if (sat(Environment currentModel, Universe uni, Environment () nextModel, void () stop) := result) {
		renderModel(uni, currentModel, nextModel, stop);
	} else {
		println("Not satisfiable, can not visualize");
	}	
}

void testRiverCrossingProblem() = translateAndVis(|project://allealle/examples/relational/rivercrossing.alle|);

void translateAndVis(loc problem) { 
  Problem p = implodeProblem(problem);
  ModelFinderResult result = checkInitialSolution(p);
  
  if (sat(Environment currentModel, Universe uni, Environment () nextModel, void () stop) := result) {
    renderModel(uni, currentModel, nextModel, stop);
  } else {
    println("Not satisfiable, can not visualize");
  } 
  
}

