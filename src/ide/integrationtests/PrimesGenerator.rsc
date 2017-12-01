module ide::integrationtests::PrimesGenerator

import List;
import IO;

void generatePrimes(int upperBound) {
  str problem = "Num (1 :: val:int)  = {<intercalate(",", ["\<n<i>,<i>\>" | i <- [1..upperBound+1]])>}
                'One (1)             = {\<n1\>}
                'Prime (1)          \<= {\<n1\>..\<n<upperBound>\>} 
                '
                'forall n:Num\\One | (exists n\':Num\\(n+One) | n\'::val \< n::val && n::val % n\'::val = 0) \<=\> not (n in Prime)";
  
  writeFile(|project://allealle/examples/int/primes.alle|, problem);
  println("Done generating primes example for <upperBound> numbers");  
}

list[int] calculatePrimesImperative(int upperBound) {
  list[int] primes = [];
  
  for (int i <- [2..upperBound]) {
    bool isPrime = true;
    for (int j <- [2..i]) {
      if (i % j == 0) {
        isPrime = false;
        break;
      }
    }
    
    if (isPrime) { 
      primes += i;
    }
  }
  
  return primes;
}
