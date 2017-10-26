module util::MemoCacheClearer

@reflect @javaClass{util.MemoCacheClearer}
java void clearMemoCache(set[str] modules, bool debug = false);

@javaClass{util.MemoCacheClearer}
java void gc();

void clearCacheAndGc(set[str] modules, bool debug = false) {
  clearMemoCache(modules, debug = debug);
  gc();
}
