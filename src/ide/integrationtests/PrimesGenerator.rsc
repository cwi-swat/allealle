module ide::integrationtests::PrimesGenerator

import List;
import IO;

void generatePrimes(int upperBound) {
  str genTuples() = intercalate(",", ["\<n<i>\>" | int i <- [1..upperBound+1]]);
  
  str problem = "{<intercalate(",", ["n<i>{val(int)=<i>}" | int i <- [1..upperBound+1]])>}
                '
                'Num:1    [{<genTuples()>},{<genTuples()>}]
                'One:1    [{\<n1\>},{\<n1\>}]
                'Primes:1 [{},{<genTuples()>}]
                '
                'Primes in Num
                'One in Num
                '
                'forall p:Num | (exists n:Num\\(p++One) | p::val % n::valgit push --set-upstream origin no-preprocessing = 0) \<=\> not (p in Primes)";
  
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

list[int] calculatePrimesFunctional(1) = [1];