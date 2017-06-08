module tests::AllTests
 
extend logic::tests::BooleanTester;
extend logic::tests::PropositionalTester;

extend theories::tests::binderTests::JoinTester;
extend theories::tests::binderTests::ProductTester;
extend theories::tests::binderTests::TransposeTester;
 
extend theories::tests::translatorTests::CardinalityTester;
//extend relational::tests::translatorTests::ComprehensionTester;
extend theories::tests::translatorTests::DifferenceTester;
extend theories::tests::translatorTests::EqualityTester;
extend theories::tests::translatorTests::JoinTester; 
extend theories::tests::translatorTests::NegationTester;
extend theories::tests::translatorTests::SubsetTester;
extend theories::tests::translatorTests::UniversalTester; 