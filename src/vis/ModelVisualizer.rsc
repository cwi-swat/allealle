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
import List;
import Set;

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
							}) | str name <- getNaryRelations(model), str edgeName := name]),
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

set[str] getNaryRelations(Environment model) = {relName | str relName <- model, Binding binding := model[relName], size(getOneFrom(binding<0>)) > 1};

Figure visualizeModel(Universe universe, Environment model, DisplayOptions disOpt) {
	if (model == ()) {
		return text("No more models available", size(100));
	}

	rel[Atom, str] unaryRels = {<a, relName> | str relName <- model, map[Index,Formula] binding := model[relName], idx:[Atom a] <- binding, model[relName][idx] == \true()};
	
	rel[list[Atom], str] naryRels = {<idx, relName> | str relName <- model, relName notin disOpt.filteredEdges, Binding binding := model[relName], size(getOneFrom(binding)) > 1, Index idx <- binding, model[relName][idx] == \true()};

	Figures nodes = [n | Atom a <- universe.atoms, just(Figure n) := buildAtomNode(a, unaryRels, disOpt)];
	nodes += [buildEdgeLabel(a,b,i,relName) | <Index idx, str relName> <- naryRels, int i <- [0 .. size(idx)-1], Atom a := idx[i], Atom b := idx[i+1]];
  
	Edges edges = [edge(a, labelId), edge(labelId, b, triangle(round(10 * disOpt.scale), fillColor("black"))) | <Index idx, str relName> <- naryRels, int i <- [0 .. size(idx)-1], Atom a := idx[i], Atom b := idx[i+1], str labelId := "<relName>_<a>_<b>_step<i>"];
	
	return graph(nodes, edges, gap(round(20 * disOpt.scale)), hint("layered"));
}

Figure buildEdgeLabel(Atom from, Atom to, int index, str relName) =
	box(text(relName), id("<relName>_<from>_<to>_step<index>"), lineWidth(0));

Maybe[Figure] buildAtomNode(Atom a, rel[Atom, str] unaryRelations, DisplayOptions disOpt) {
	Figure getLabel() = vcat([text("\<<r>\>", center()) | str r <- unaryRelations[a]] + [text(a, [fontBold(true), center()])]); 
	
	if (unaryRelations[a] == {}) {
		return nothing();
	} else {
		return just(ellipse(getLabel(), fillColor("white"), size(round(50 * disOpt.scale)), id(a), lineWidth(1.5)));
	}			
}



