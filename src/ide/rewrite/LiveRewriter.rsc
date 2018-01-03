module ide::rewrite::LiveRewriter

import ParseTree;

lrel[loc,str] rewrite(&T<:Tree input, &R (&R) rule) {
  lrel[loc,str] updates = [];
  
  bool update(&R p) {
    pp = rule(p);
    if ("<p>" != "<pp>") {
      updates += <p@\loc,"<pp>">;
      return true;
    } 
    return false;
  }
  
  input = visit (input) {
    case &R e => rule(e) when update(e) 
  }
    
  return updates;
}