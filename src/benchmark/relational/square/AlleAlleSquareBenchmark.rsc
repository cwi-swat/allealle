module benchmark::relational::square::AlleAlleSquareBenchmark

extend benchmark::AlleAlleBenchmark;

void runSquareBenchmark(str postfix = "") 
  = runBenchmark([4..11], "relational", "square", true, postfix = postfix);

str constructRels(int config) 
  = "Num (nId: id, val: int) = {\<n1,?\>,\<n2,?\>}";
   
str getConstraints(int config) 
  = "∀ n ∈ Num | some n where val \> <config>
    '∃ n1 ∈ Num, n2 ∈ Num ∖ n1 | some (n1 ⨯ n2[nId as n2Id, val as val2]) where val = val2 * val2";
