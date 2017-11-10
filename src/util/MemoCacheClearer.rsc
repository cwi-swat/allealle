module util::MemoCacheClearer

import util::Reflective;
import IO;

void clearMemoCache(set[str] modules, bool debug = false) = inCompiledMode() ? clearCompiledMemoCache(modules, debug) : clearInterpretedMemoCache(modules, debug);

@reflect @javaClass{util.InterpretedMemoCacheClearer}
java void clearInterpretedMemoCache(set[str] modules, bool debug);

void clearCompiledMemoCache(set[str] modules, bool debug) {
  if (debug) {
    println("Clearing memo cache of compiled functions");
  }
  
  for (str m <- modules) {
    list[str] funcs = clearMemos(m);
    
    if (debug) {
      for (f <- funcs) {
        println("Cleared the compiled memo cache of the \'<f>\' function");
      }
    }
  }
  
  if (debug) {
    println("Done clearing memo cache of compiled functions");
  }
}