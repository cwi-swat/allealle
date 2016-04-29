module tests::PigeonHoleTester

extend tests::SmtIntegrationTestBase;

import IO;

str generatePigeonProblem(int lbPigeons, int ubPigeons, int nrOfHoles) = 
	"{<intercalate(",",["p<i>" | i <- [1..ubPigeons+1]])>,<intercalate(",",["h<i>" | i <- [1..nrOfHoles+1]])>} 
	'Pigeon:1 [{<intercalate(",",["\<p<i>\>" | i <- [1..lbPigeons+1]])>},{<intercalate(",",["\<p<i>\>" | i <- [1..ubPigeons+1]])>}]
	'Hole:1 [{},{<intercalate(",",["\<h<i>\>" | i <- [1..nrOfHoles+1]])>}]
	'nest:2 [{},{<intercalate(",",["\<p<i>,h<j>\>" | i <- [1..ubPigeons+1], j <- [1..nrOfHoles+1]])>}]
	'nest in Pigeon -\> Hole
	'forall h:Hole | one nest.h
	'";
	//'forall p:Pigeon | one p.nest	
	
void testPigeonHoleWithNPigeonsAndHoles(int n) =
	executeTest("Starting with pigeon hole problem with <n> pigeons and holes", generatePigeonProblem(0,n,n));		
void testPigeonHoleWithNPigeonsAndMHoles(int n, int m) =
	executeTest("Starting with pigeon hole problem with <n> pigeons and <m> holes", generatePigeonProblem(0,n,m));		
void testPigeonHoleWithExactlyNPigeonsAndMHoles(int n, int m) =
	executeTest("Starting with pigeon hole problem with <n> pigeons and <m> holes", generatePigeonProblem(n,n,m));		

	
void testPigeonHoleWith2PigeonsAndHoles() = testPigeonHoleWithNPigeonsAndHoles(2);
void testPigeonHoleWith5PigeonsAndHoles() = testPigeonHoleWithNPigeonsAndHoles(5);

void testPigeonHoleWith5PigeonsAnd4Holes() = testPigeonHoleWithNPigeonsAndMHoles(5,4);
void testPigeonHoleWithExactly2PigeonsAnd1Holes() = testPigeonHoleWithExactlyNPigeonsAndMHoles(2,1);

