module ide::vis::ModelVisualizer

import logic::Propositional;
import logic::Integer;

import ide::CombinedAST;

import theories::Binder;
import theories::SMTInterface;

import vis::Figure;
import vis::Render;

import util::Maybe; 
import util::Math;

import Map; 
import List;  
import Set;
import Node;
import String;
 
import IO;

data DisplayOptions = options(real scale = 1.0, set[str] filteredEdges = {});

data DisplayModus = textual() | visual();

FProperty myLeft() = halign(0.0);

void renderModel(Universe universe, Model model, Model (Theory) nextModel, void () stop) {
	DisplayOptions disOpt = options();
	DisplayModus disModus = textual();
	
	Model currentModel = model;

	void switchDisplay() { 
    switch(disModus) {
      case visual(): disModus = textual(); 
      case textual(): disModus = visual();
    }
    
    r();
  }
  
  set[Theory] theoriesInModel = {delAnnotations(t) | /Theory t := currentModel}; 
 
  str toStr(intTheory()) = "integer";
   
	Figure showButtons() = currentModel != empty() ?
		hcat(
		  [button("Next relational model", void () { currentModel = nextModel(relTheory()); r();})] + 
		  [button("Next <toStr(t)> model", void () { currentModel = nextModel(t); r();}) | Theory t <- theoriesInModel] +
			[button("Stop", stop)]
		) :
		hcat([
			button("Stop", stop)
		]); 
				
	Figure showToggle() {
	  switch(disModus) {
	    case visual():  return button("Current display: Visual\n Switch to textual", switchDisplay);
	    case textual(): return button("Current display: Textual\n Switch to visual", switchDisplay);
	  }
  }
  
	Figure showDisplayOptions() = disModus == visual() ?
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
		]) : hcat([]);
	

	Figure showModel() =
	 disModus == visual() ? 
	   scrollable(visualizeModel(universe, currentModel, disOpt)) :
	   scrollable(box(vcat(textualizeModel(currentModel) + box(lineWidth(0)), align(0,0)), lineWidth(0), hshrink(0.98))); 

			
	Figures textualModel = textualizeModel(model);
			
	void r() {  
		render("Model visualizer", 
			vcat([
				box(
					hcat([
					  box(showToggle(), hshrink(0.20)),
						box(showDisplayOptions(), hshrink(0.40)),
						showButtons()
					]),
					vshrink(0.10)
				),
			 showModel()
			]));
	}

	r();

}

set[str] getNaryRelations(Model model) = {name | r:nary(str name, set[VectorAndVar] _, bool _) <- model.relations};

Figure visualizeModel(Universe universe, Model model, DisplayOptions disOpt) {
	if (model == empty()) {
		return text("No more models available", size(100));
	}

  bool contains(Atom a, Relation r) = true when VectorAndVar vv <- r.relation, a in vv.vector;
  default bool constains(Atom a, Relation r) = false; 

	rel[ModelAtom, Relation] unaryRels = {<ma, r> | ModelAtom ma <- model.visibleAtoms, r:unary(str relName, set[VectorAndVar] relation, bool inBase) <- model.relations, ma.name == relName, contains(ma.name, r)};
	rel[list[Atom], Relation] naryRels = {<vv.vector, r> | r:nary(str name, set[VectorAndVar] relation, bool inBase) <- model.relations, VectorAndVar vv <- relation};

	Figures nodes = [buildAtomNode(ma, unaryRels, disOpt) | ModelAtom ma <- model.visibleAtoms];
	nodes += [buildEdgeLabel(a,b,i,r.name) | <list[Atom] idx, Relation r> <- naryRels, int i <- [0 .. size(idx)-1], Atom a := idx[i], Atom b := idx[i+1]];
  
	Edges edges = [edge(a, labelId), edge(labelId, b, triangle(round(10 * disOpt.scale), fillColor("black"))) | <list[Atom] idx, Relation r> <- naryRels, int i <- [0 .. size(idx)-1], Atom a := idx[i], Atom b := idx[i+1], str labelId := "<r.name>_<a>_<b>_step<i>"];
	
	return graph(nodes, edges, gap(round(20 * disOpt.scale)), hint("layered"));
} 

Figure buildEdgeLabel(Atom from, Atom to, int index, str relName) =
	box(text(relName), id("<relName>_<from>_<to>_step<index>"), lineWidth(0));

Figure buildAtomNode(ModelAtom ma, rel[ModelAtom, Relation] unaryRelations, DisplayOptions disOpt) {
	Figure getLabel() = vcat([text("\<<r.name>\>", center()) | Relation r <- unaryRelations[ma]] + 
	                         [text(ma.name, [fontBold(true), center()])] + 
	                         [text("<i>", [fontItalic(true), center()]) | ma has val, intExpr(intLit(int i)) := ma.val]); 
	
  return ellipse(getLabel(), fillColor("white"), size(round(50 * disOpt.scale)), id(ma.name), lineWidth(1.5));
}

Figures textualizeModel(Model model) {
  if (model == empty()) {
    return [text(""), text("No more models available", fontBold(true), myLeft())];
  }
  
  bool vectorSort(VectorAndVar a, VectorAndVar b ) {
    for (int i <- [0..size(a.vector)]) {
      if (a.vector[i] > b.vector[i]) { return false; }
      else if (a.vector[i] < b.vector[i]) { return true; }  
    }
    
    return false;
  }
  
  str intTheoryValue(str atom) = " (<i>)" when ModelAtom a <- model.visibleAtoms, a.name == atom, a has theory, a.theory == intTheory(), intExpr(intLit(int i)) := a.val;
  default str intTheoryValue(str atom) = "";
  
  Figures m = [text("")];
  list[str] sortedRel = sort(toList({r.name | Relation r <- model.relations}));
  
  for (str relName <- sortedRel, !startsWith(relName, "_"), Relation r <- model.relations, r.name == relName) {
    m += text("<relName>:", fontBold(true), fontItalic(true), myLeft());
    
    list[VectorAndVar] sortedIndices = sort(toList(r.relation), vectorSort);
    
    for (VectorAndVar idx <- sortedIndices) {
      m += text("  <intercalate(" -\> ", ["<idx.vector[i]><intTheoryValue(idx.vector[i])>" | int i <- [0..size(idx.vector)]])>", myLeft());
    } 
        
    m += text("");
  }
  
  return m;
}



