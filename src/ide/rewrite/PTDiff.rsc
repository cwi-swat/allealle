module ide::rewrite::PTDiff

import ide::rewrite::LCS;

import ParseTree;
import String;
import List;
import IO;
import util::Math;

lrel[loc, str] ptDiff(Tree old, Tree new) {
  diff = [];

  if (old is amb || new is amb) {
    throw "Ambiguous nodes not supported";
  }
  
  assert old has prod && new has prod;

  if (old.prod != new.prod) {
    return [<old@\loc, "<new>">];  
  }

  bool ptEq(Tree t1, Tree t2) = t1.prod == t2.prod;
  

  loc getLoc(Tree parent, Tree kid, int pos) {
    if (kid@\loc?) {
      return kid@\loc;
    }
    args = parent.args;
    src = ( "" | it + "<a>" | Tree a <- args[0..pos] );
    return parent@\loc[offset=parent@\loc.offset+size(src)];
  }

  if (old.prod is regular, !(old.prod.def is alt)) {
    mx = lcsMatrix(old.args, new.args, ptEq);
    ds = getDiff(mx, old.args, new.args, size(old.args), size(new.args), ptEq);
    int offset = 0;
    for (Diff d <- ds) {
      switch (d) {
        case add(Tree v, int pos): { 
          // todo: this requires newtree to have locs!!!
          diff += [<getLoc(new, v, pos)[length=0], "<v>">];
        }
        
        case remove(Tree v, int pos): {
          oldLoc = getLoc(old, v, pos);
          diff += [<oldLoc[length=size("<v>")], "">];
        }
          
        case same(Tree t1, Tree t2): {
          if (isToken(t1.prod.def)) {
            if (!realEq(t1, t2)) {
              diff += [<t1@\loc, "<t2>">];
            }
          }
          else {
            diff += ptDiff(t1, t2);
          }
        }
      }
    }
    return diff;
  }
  
  assert size(old.args) == size(new.args);
  
  for (int i <- [0..size(old.args)]) {
    Tree oldArg = old.args[i];
    Tree newArg = new.args[i];

    if (isToken(oldArg.prod.def)) {
      if (!realEq(newArg, oldArg)) {
      diff += [<getLoc(old, oldArg, i)[length=size("<oldArg>")], "<newArg>">];
    }
    }
    else {
      diff += ptDiff(oldArg, newArg);
    }
  }  
  
  return diff;
}


bool realEq(appl(Production p, list[Tree] args1), appl(p, list[Tree] args2))
  = size(args1) == size(args2) && ( true | it && realEq(args1[i], args2[i]) | int i <- [0..size(args1)] );
  
bool realEq(char(int i), char(int j)) = i == j;  
  
default bool realEq(Tree _, Tree _) = false; 

bool isToken(label(_, Symbol s)) = isToken(s);

bool isToken(lex(_)) = true;

bool isToken(layouts(_)) = true;

bool isToken(lit(_)) = true;

bool isToken(cilit(_)) = true;

default bool isToken(Symbol _) = false;