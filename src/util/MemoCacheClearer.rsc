module util::MemoCacheClearer

@reflect @javaClass{util.MemoCacheClearer}
java void clearMemoCache(set[str] modules, bool debug = false);