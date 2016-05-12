module vis::ModelVisualizer

import logic::Propositional;

import orig::Translator;
import orig::AST;

import vis::Figure;
import vis::Render;

import util::Maybe;

import Map;

import IO;

void renderModel(Universe universe, Environment model, Environment () nextModel, void () stop) {
	Environment currentModel = model;

	void visualizeNextModel() { currentModel = nextModel(); r();} 
	
	Figure showButtons() = currentModel != () ?
		hcat([
			button("Next model", visualizeNextModel),
			button("Stop", stop)
		]) :
		hcat([
			button("Stop", stop)
		]); 
			
	void r() = 
		render("Model visualizer", 
			vcat([
				box(
					showButtons(),
					vshrink(0.10)
				),
				scrollable(visualizeModel(universe, currentModel))
			]));

	r();
}

Figure visualizeModel(Universe universe, Environment model) {
	if (model == ()) {
		return text("No more models available", size(100));
	}

	rel[Atom, str] unaryRels = {<a, relName> | Atom a <- universe.atoms, str relName <- model, /idx:<a> := model[relName], model[relName][idx] == \true()};
	rel[Atom, Atom, str] binaryRels = {<a, b, relName> | Atom a <- universe.atoms, Atom b <- universe.atoms, str relName <- model, /idx:<a,b> := model[relName], model[relName][idx] == \true()};

	Figures nodes = [n | Atom a <- universe.atoms, just(Figure n) := buildAtomNode(a, unaryRels)];
	nodes += [buildEdgeLabel(r<0>,r<1>,r<2>) | r <- binaryRels];
	Edges edges = [edge(r<0>, labelId), edge(labelId, r<1>, triangle(10, fillColor("black"))) | r <- binaryRels, str labelId := r<2> + "_" + r<0> + "_" + r<1>];
	
	return graph(nodes, edges, gap(20), hint("layered"));
}

Figure buildEdgeLabel(Atom from, Atom to, str relName) =
	box(text(relName), id("<relName>_<from>_<to>"), lineWidth(0));

Maybe[Figure] buildAtomNode(Atom a, rel[Atom, str] unaryRelations) {
	Figure getLabel() = vcat([text("\<<r>\>", center()) | str r <- unaryRelations[a]] + [text(a, [fontBold(true), center()])]); 
	
	if (unaryRelations[a] == {}) {
		return nothing();
	} else {
		return just(ellipse(getLabel(), fillColor("white"), size(50), id(a), lineWidth(1.5)));
	}			
}



