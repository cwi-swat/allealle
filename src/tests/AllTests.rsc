module tests::AllTests
 
extend logic::tests::BooleanTester;
extend logic::tests::PropositionalTester;

extend theories::relational::tests::binderTests::JoinTester;
extend theories::relational::tests::binderTests::ProductTester;
extend theories::relational::tests::binderTests::TransposeTester;
 
extend theories::relational::tests::translatorTests::CardinalityTester;
//extend relational::tests::translatorTests::ComprehensionTester;
extend theories::relational::tests::translatorTests::DifferenceTester;
extend theories::relational::tests::translatorTests::EqualityTester;
extend theories::relational::tests::translatorTests::JoinTester; 
extend theories::relational::tests::translatorTests::NegationTester;
extend theories::relational::tests::translatorTests::SubsetTester;
extend theories::relational::tests::translatorTests::UniversalTester; 