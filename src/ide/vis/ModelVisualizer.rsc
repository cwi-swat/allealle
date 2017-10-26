module ide::vis::ModelVisualizer

import ide::CombinedAST;

import translation::Binder;
import translation::SMTInterface;

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

data VisNode = visNode(str id, set[str] unaryRels, map[str, str] attributeVals);
data VisEdge = visEdge(str naryRel, Id from, Id to, int pos, map[str, str] attributeVals);

FProperty myLeft() = halign(0.0);

void renderModel(Model model, Model (Domain) nextModel, void () stop) {
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
  
  set[Domain] domainsInModel = {delAnnotations(d) | /Domain d := currentModel}; 
 
  str toStr(\int()) = "integer";
   
	Figure showButtons() = currentModel != empty() ?
		hcat(
		  [button("Next relational model", void () { currentModel = nextModel(id()); r();})] + 
		  [button("Next <toStr(d)> model", void () { currentModel = nextModel(d); r();}) | Domain d <- domainsInModel] +
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
							   }) | str name <- {name | nary(str name, _) <- model.relations}, str edgeName := name]),
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
	   scrollable(visualizeModel(currentModel, disOpt)) :
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

str val2Str(lit(posInt(int i))) = "<i>";
str val2Str(lit(negInt(int i))) = "-<i>";

Figure visualizeModel(Model model, DisplayOptions disOpt) {
	if (model == empty()) { 
		return text("No more models available", size(100));
	}

  set[VisNode] buildVisNodes() {
    map[Id, VisNode] nodes = ();
    
    for (unary(str relName, set[ModelTuple] tuples) <- model.relations, ModelTuple t <- tuples, [Id id] := t.idx.idx) {
      map[str,str] attVals = (att.name : val2Str(att.val) | ModelAttribute att <- t.attributes);
      
      if (id in nodes) {
        nodes[id] = visNode(id, nodes[id].unaryRels + relName, nodes[id].attributeVals + attVals);
      } else {
        nodes[id] = visNode(id, {relName}, attVals);
      }           
    }
    
    return nodes<1>;
  }

  set[VisEdge] buildVisEdges() {
    set[VisEdge] edges = {};
    
    for (nary(str relName, set[ModelTuple] tuples) <- model.relations, relName notin disOpt.filteredEdges, ModelTuple t <- tuples) {
      map[str,str] attVals = (att.name : val2Str(att.val) | ModelAttribute att <- t.attributes);
      Index idx = t.idx.idx;

      for (int i <- [0..size(idx)-1]) {
        edges += visEdge(relName, idx[i], idx[i+1], i, attVals);
      }        
    }  
    
    return edges;
  }
  
  set[VisNode] vn = buildVisNodes();
  set[VisEdge] en = buildVisEdges();
  
	Figures nodes = [displayNode(n, disOpt) | VisNode n <- vn] + [displayEdgeNode(e, disOpt) | VisEdge e <- en];
	Edges edges = [edge(e.from, labelId), edge(labelId, e.to, triangle(round(10 * disOpt.scale), fillColor("black"))) | VisEdge e <- en, str labelId := "<e.naryRel>_<e.from>_<e.to>_<e.pos>"];

	return graph(nodes, edges, gap(round(20 * disOpt.scale)), hint("layered"));
} 

Figures displayAttributes(map[str,str] attributes) {
  if (attributes == ()) {
    return [];
  }
  
  return [text("(<intercalate(",", ["<attName>:<attributes[attName]>" | str attName <- attributes])>)", center())];
}

Figure displayNode(VisNode n, DisplayOptions disOpt) 
  = ellipse(vcat([text(n.id, [fontBold(true), center()])] + [text("\<<relName>\>", center()) | str relName <- n.unaryRels] + displayAttributes(n.attributeVals)), 
            fillColor("white"), size(round(50 * disOpt.scale)), FProperty::id(n.id), lineWidth(1.5));

Figure displayEdgeNode(VisEdge e, DisplayOptions disOpt)
	= box(vcat([text(e.naryRel, center())] + displayAttributes(e.attributeVals)), 
	    FProperty::id("<e.naryRel>_<e.from>_<e.to>_<e.pos>"), lineWidth(0));
	 

Figures textualizeModel(Model model) {
  if (model == empty()) {
    return [text(""), text("No more models available", fontBold(true), myLeft())];
  }
  
  bool indexSort(Index a, Index b ) {
    for (int i <- [0..size(a)]) {
      if (a[i] < b[i]) { return true; }
      else if (a[i] > b[i]) { return false; }
    }   
    return false;
  }
  
  str displayAttributes([]) = "";
  default str displayAttributes(list[ModelAttribute] attributes) = " (<intercalate(",", ["<a.name>:<val2Str(a.val)>" | a <- attributes])>)";
  
  Figures m = [text("")];
  list[str] sortedRel = sort(toList({r.name | ModelRelation r <- model.relations}));
  
  for (str relName <- sortedRel, ModelRelation r <- model.relations, r.name == relName) {
    m += text("<relName>:", fontBold(true), fontItalic(true), myLeft());
    
    list[Index] sortedIndices = sort([t.idx.idx | ModelTuple t <- r.tuples], indexSort);
    
    for (Index idx <- sortedIndices, ModelTuple t <- r.tuples, t.idx.idx == idx) {
      m += text("  <intercalate(" -\> ", [idx[i] | int i <- [0..size(idx)]])> <displayAttributes(t.attributes)>", myLeft());
    } 
        
    m += text("");
  }
  
  return m;
}



