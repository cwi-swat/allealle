module vis::ModelVisualizer

import logic::Propositional;
import logic::Integer;

import orig::FormulaTranslator;
import orig::ExpressionTranslator;
import orig::AST;

import vis::Figure;
import vis::Render;

import util::Maybe;
import util::Math;

import Map;

import IO;

data DisplayOptions = options(real scale = 1.0, set[str] filteredEdges = {});

void renderModel(Universe universe, Environment model, Environment () nextModel, void () stop) {
	DisplayOptions disOpt = options();
	
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
	
	Figure showDisplayOptions() = 
		hcat([
			box(
				vcat([
					text("Visualization options:", fontBold(true)),
					box(
						hcat([checkbox(name, name notin disOpt.filteredEdges, void (bool checked) {
							disOpt = options(scale = disOpt.scale, filteredEdges = !checked ? disOpt.filteredEdges + edgeName : disOpt.filteredEdges - edgeName); 
							r();
							}) | str name <- getBinaryRelations(model), str edgeName := name]),
						hshrink(0.98), center()),
					text("Zoom: <precision(disOpt.scale, 2)>"),
					scaleSlider(int () { return  0; }, int () { return 100; }, int () { return round(disOpt.scale * 50.); }, void (int cur) {
						disOpt = options(scale = toReal(cur) / 50., filteredEdges = disOpt.filteredEdges);
						r();
					}, hshrink(0.8))
				]),	
				shrink(0.98),
				center()
			)
		]);
			
	void r() = 
		render("Model visualizer", 
			vcat([
				box(
					hcat([
						box(showDisplayOptions(), hshrink(0.40)),
						showButtons()
					]),
					vshrink(0.10)
				),
				scrollable(visualizeModel(universe, currentModel, disOpt))
			]));

	r();
}

set[str] getBinaryRelations(Environment model) = {relName | str relName <- model, /<_,_,relTheory()> := model[relName]};

Figure visualizeModel(Universe universe, Environment model, DisplayOptions disOpt) {
	if (model == ()) {
		return text("No more models available", size(100));
	}

	rel[Atom, str] unaryRels = {<a, relName> | Atom a <- universe.atoms, str relName <- model, /idx:<a, relTheory()> := model[relName], model[relName][idx] == \true()};
	rel[Atom, int] unaryIntVals = {<a, i> | Atom a <- universe.atoms, str relName <- model, /idx:<a, intTheory()> := model[relName], \int(int i) := model[relName][idx]};
	
	rel[Atom, Atom, str] binaryRels = {<a, b, relName> | Atom a <- universe.atoms, Atom b <- universe.atoms, str relName <- model, /idx:<a,b, relTheory()> := model[relName], relName notin disOpt.filteredEdges, model[relName][idx] == \true()};

	Figures nodes = [n | Atom a <- universe.atoms, just(Figure n) := buildAtomNode(a, unaryRels, unaryIntVals, disOpt)];
	nodes += [buildEdgeLabel(r<0>,r<1>,r<2>) | r <- binaryRels];
	Edges edges = [edge(r<0>, labelId), edge(labelId, r<1>, triangle(round(10 * disOpt.scale), fillColor("black"))) | r <- binaryRels, str labelId := r<2> + "_" + r<0> + "_" + r<1>];
	
	return graph(nodes, edges, gap(round(20 * disOpt.scale)), hint("layered"));
}

Figure buildEdgeLabel(Atom from, Atom to, str relName) =
	box(text(relName), id("<relName>_<from>_<to>"), lineWidth(0));

Maybe[Figure] buildAtomNode(Atom a, rel[Atom, str] unaryRelations, rel[Atom, int] unaryIntVals, DisplayOptions disOpt) {
	Figure getLabel() = vcat([text("\<<r>\>", center()) | str r <- unaryRelations[a]] + [text(a, [fontBold(true), center()])] + [text("<i>", [fontItalic(true), center()]) | int i <- unaryIntVals[a]]); 
	
	if (unaryRelations[a] == {}) {
		return nothing();
	} else {
		return just(ellipse(getLabel(), fillColor("white"), size(round(50 * disOpt.scale)), id(a), lineWidth(1.5)));
	}			
}



