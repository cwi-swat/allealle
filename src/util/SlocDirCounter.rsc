module util::SlocDirCounter

import analysis::grammars::LOC;
import util::Reflective;
import IO;
import String;

int countSlocInDir(loc base) {
  if (!isDirectory(base)) {
    if (base.extension == "rsc") {
      int sloc = countSLOC(parseModule(base));
      println("<base.path>; <sloc>");
      return sloc;
    } 
    else {
      return 0;
    }
  } else {
    int sloc = 0;

    for (file <- base.ls, !endsWith(file.path, "tests")) {
      sloc += countSlocInDir(file);
    } 
    
    return sloc;
  }

} 