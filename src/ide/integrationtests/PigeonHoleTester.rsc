module ide::integrationtests::PigeonHoleTester

import ide::integrationtests::ProblemRunner;

import IO;
import List;

str generatePigeonProblem(int lbPigeons, int ubPigeons, int nrOfHoles) = 
	"Pigeon (1) = {<intercalate(",",["\<p<i>\>" | i <- [1..nrOfPigeons+1]])>}
  'Hole (1) = {<intercalate(",",["\<h<i>\>" | i <- [1..nrOfHoles+1]])>}
  'nest (2) \<= {<intercalate(",",["\<p<i>,h<j>\>" | i <- [1..nrOfPigeons+1], j <- [1..nrOfHoles+1]])>}
  '
  'forall p:Pigeon | one p.nest 
  'forall h:Hole | some nest.h";
	
void testPigeonHoleWithNPigeonsAndHoles(int n)                = translateAndSolve(generatePigeonProblem(0,n,n), 1);		
void testPigeonHoleWithNPigeonsAndMHoles(int n, int m)        = translateAndSolve(generatePigeonProblem(0,n,m), 1);		
void testPigeonHoleWithExactlyNPigeonsAndMHoles(int n, int m) =	translateAndSolve(generatePigeonProblem(n,n,m), 1);		

	
void testPigeonHoleWith2PigeonsAndHoles() = testPigeonHoleWithNPigeonsAndHoles(2);
void testPigeonHoleWith5PigeonsAndHoles() = testPigeonHoleWithNPigeonsAndHoles(5);

void testPigeonHoleWith5PigeonsAnd4Holes() = testPigeonHoleWithNPigeonsAndMHoles(5,4);
void testPigeonHoleWithExactly2PigeonsAnd1Holes() = testPigeonHoleWithExactlyNPigeonsAndMHoles(1,1);

 