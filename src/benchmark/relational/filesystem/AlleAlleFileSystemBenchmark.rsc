module benchmark::relational::filesystem::AlleAlleFileSystemBenchmark

extend benchmark::AlleAlleBenchmark;

void runFileSystemBenchmark(str postfix = "") 
  = runBenchmark([5..10], "relational", "filesystem", true, postfix = postfix); 

str constructRels(int config) {
  str rels = "Object (oId: id)  \<= {<intercalate(",", ["\<o<i>\>" | i <- [0..config]])>}
             'Name (nId: id)    \<= {<intercalate(",", ["\<n<i>\>" | i <- [0..config]])>}
             'File (oId: id)    \<= {<intercalate(",", ["\<o<i>\>" | i <- [0..config]])>}
             'Dir (oId: id)     \<= {<intercalate(",", ["\<o<i>\>" | i <- [0..config]])>}
             '
             'entries (oId: id, dId: id) \<= {<intercalate(",", ["\<o<i>,d<j>\>" | i <- [0..config], j <- [0..config]])>}
             'parent (oId: id, parent: id) \<= {<intercalate(",", ["\<o<i>,o<j>\>" | i <- [0..config], j <- [0..config]])>}
             '
             'Root (oId: id)     = {\<o0\>}
             'Cur (oId: id)     \<= {<intercalate(",", ["\<o<i>\>" | i <- [0..config]])>}
             '
             'DirEntry (dId: id) \<= {<intercalate(",", ["\<d<i>\>" | i <- [0..config]])>}
             'entryName(dId:id, nId:id) \<= {<intercalate(",", ["\<d<i>,n<j>\>" | i <- [0..config], j <- [0..config]])>}
             'contents (dId:id, oId:id) \<= {<intercalate(",", ["\<d<i>,o<j>\>" | i <- [0..config], j <- [0..config]])>}";
             
    return rels;
}

str getConstraints(int config)
  = "Object = File ∪ Dir
    'no File ∩ Dir
    '
    'Root ⊆ Dir
    'Cur ⊆ Dir
    'no Root ∩ Cur
    '
    'one Root
    'no (Root ⨝ parent)
    '
    'entries ⊆ Dir ⨯ DirEntry
    '
    '// parent is a partial function from Dir -\> Dir
    'parent ⊆ Dir ⨯ Dir[oId as parent]
    '∀ d ∈ Dir | lone d ⨝ parent
    '
    '// entryName is a function from DirEntry -\> Name
    'entryName ⊆ DirEntry ⨯ Name
    '∀ d ∈ DirEntry | one d ⨝ entryName
    '
    '// contents is a function from DirEntry -\> Object
    'contents ⊆ DirEntry ⨯ Object
    '∀ d ∈ DirEntry | one d ⨝ contents
    '
    '// All files are part of an directory
    '∀ f ∈ File | ∃ d ∈ Dir | f ⊆ ((d ⨝ entries)[oId as parentId] ⨝ contents)[oId]
    '
    '∀ d ∈ Dir | 
    '  ((d ⨝ parent)[parent][parent as oId] = ((d ⨝ contents)[dId] ⨝ entries)[oId]) ∧ 
    '  (∀ e1 ∈ (d ⨝ entries)[dId], e2 ∈ (d ⨝ entries)[dId] | (e1 ⨝ entryName)[nId] = (e2 ⨝ entryName)[nId] ⇒ e1 = e2) ∧ 
    '  (¬(d ⊆ (d ⨝ ^parent)[parent][parent as oId])) ∧ 
    '  ((¬ d = Root) ⇒ Root ⊆ (d ⨝ ^parent)[parent][parent as oId]) 
    '    
    '∀ d ∈ DirEntry | one (d ⨝ entries) 
    '
    '∀ d ∈ Dir ∖ Root | one d ⨝ parent
    '
    '¬ (∀ d ∈ Dir | lone d ⨝ contents)";