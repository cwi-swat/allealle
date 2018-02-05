module ide::vis::ModelVisualizer

import ide::CombinedAST;

import translation::Relation;
import translation::SMTInterface;

import smtlogic::Core;

import vis::Figure;
import vis::Render;
import vis::KeySym;

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

FProperty myLeft() = halign(0.05);

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
 
  str toStr(id()) = "id";
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
	   vscrollable(textualizeModel(currentModel)); 

			
	Figure textualModel = textualizeModel(model);
			
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
  
  return [text("[<intercalate(",", ["<attName>:<attributes[attName]>" | str attName <- attributes])>]", center())];
}

Figure displayNode(VisNode n, DisplayOptions disOpt) 
  = ellipse(vcat([text(n.id, [fontBold(true), center()])] + [text("\<<relName>\>", center()) | str relName <- n.unaryRels] + displayAttributes(n.attributeVals)), 
            fillColor("white"), size(round(50 * disOpt.scale)), FProperty::id(n.id), lineWidth(1.5));

Figure displayEdgeNode(VisEdge e, DisplayOptions disOpt)
	= box(vcat([text(e.naryRel, center())] + displayAttributes(e.attributeVals)), 
	    FProperty::id("<e.naryRel>_<e.from>_<e.to>_<e.pos>"), lineWidth(0));
	 

str term2Str(Term val) { throw "Not yet implemented"; }

Figure textualizeModel(Model model) {
  if (model == empty()) {
    return vcat([text(""), text("No more models available", fontBold(true), myLeft())], top(), resizable(false), myLeft());
  }

  str att2Str(idAttribute(str name, str id)) = id;
  str att2Str(fixedAttribute(str name, Term val)) = term2Str(val);
  str att2Str(varAttribute(str name, Term val, str smtVarName)) = term2Str(val);

  map[str,str] sortBy = ();
  
  list[ModelTuple] sortTuples(str relName, list[ModelTuple] tuples) {
    list[str] sortByAtts = [trim(s) | str s <- split(",", sortBy[relName])];
    
    bool sortTuple(ModelTuple a, ModelTuple b) {
      if (a == b) return false;
      
      for (str att <- sortByAtts, ModelAttribute aa <- a.attributes, aa.name == att, ModelAttribute bb <- b.attributes, bb.name == att) {
        if (att2Str(aa) < att2Str(bb)) {
          return true;
        } else if (att2Str(aa) > att2Str(bb)) {
          return false;
        }   
      }
      
      return false;
    }

    return sort(tuples, sortTuple);
  }
  
  bool headingSort(tuple[str,Domain] a, tuple[str,Domain] b) {
    if (a[1] == id() && b[1] == id() && a[0] < b[0]) { return true; }
    else if (a[1] == id() && b[1] != id()) { return true; }
    else if (a[1] != id() && b[1] == id()) { return false; }
    else if (a[0] < b[0]) { return true; }
    else { return false; } 
  }
  
  bool sortOnHeading(str relName, str attribute, map[KeyModifier,bool] keysPressed) {
    println("Attribute: <attribute>, key pressed: <keysPressed>");
  }

  int rowHeight = 25;
  int rowWidth = 80;
  int nrOfCols = 5;

  Figure att2Fig(idAttribute(str name, str id), FProperty props ...) = box(text(id, props + [myLeft()]), lineWidth(1), height(rowHeight), width(rowWidth));
  Figure att2Fig(fixedAttribute(str name, Term val), FProperty props ...) = text(term2Str(val), props + [fontBold(true)]);
  Figure att2Fig(varAttribute(str name, Term val, str smtVarName), FProperty props ...) = text(term2Str(val), props);

  Figures tuple2Figs(fixedTuple(list[ModelAttribute] attributes), list[str] heading) = [att2Fig(at, fontItalic(true), fontBold(true)) | str h <- heading, ModelAttribute at <- attributes, at.name == h]; 
  Figures tuple2Figs(varTuple(list[ModelAttribute] attributes, str name), list[str] heading) = [att2Fig(at) | str h <- heading, ModelAttribute at <- attributes, at.name == h];

  Figure headingAttribute2Fig(str relName, str attribute) = box(text(attribute, fontBold(true), myLeft(), fontColor("white")), lineWidth(1), fillColor("gray"), height(rowHeight), width(rowWidth), onMouseUp(bool (int _, map[KeyModifier,bool] keysPressed) { sortOnHeading(relName, attribute, keysPressed);}));
  Figures heading2Figs(str relName, list[str] heading) = [headingAttribute2Fig(relName, h) | h <- heading];

  bool redraw = false;

  bool mustRedraw() {
    if (redraw) {
      redraw = false;
      return true;
    } else {
      return false;
    }
  }

  Figure drawTables() {
    list[Figures] cols = [[text("")] | int _ <- [0..nrOfCols]];
    int currentCol = 0;
  
    for (ModelRelation r <- sort(model.relations)) {
      Figures table = [text("<r.name>:", fontBold(true), fontItalic(true), myLeft())];
      list[str] sortedHeading = [h | str h <- sort(toList(r.heading), headingSort)<0>];
      
      if (r.name notin sortBy) {
        sortBy[r.name] = sortedHeading[0];
      }
      
      if (size(r.heading) > 1) {
        str relName = r.name;
        table += [hcat([text("Sort by:", left()), textfield(sortBy[relName],  void (str attributes) { sortBy[relName] = attributes; redraw = true; }, left(), height(10))], hgap(10))];
      }
      
      list[Figures] relBody = [];    
      for (ModelTuple t <- sortTuples(r.name, r.tuples)) {
        relBody += [tuple2Figs(t, sortedHeading)];
      } 
      
      table += grid([heading2Figs(r.name, sortedHeading)] + relBody, lineWidth(1), left(), top(), resizable(false));
      
      cols[currentCol] += table;      
      
      currentCol += 1;
      if (currentCol == nrOfCols) {
        currentCol = 0;
      }
    }
    
    return hcat([vcat(cols[i], vgap(20), endGap(true), resizable(false), top()) | int i <- [0..nrOfCols]], 
             hgap(50), hshrink(0.98), halign(0.02), top(), resizable(false));
  }
     
  return computeFigure(mustRedraw, drawTables);
}



