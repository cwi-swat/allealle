module ide::CombinedModelFinder

extend ModelFinder;

extend theories::relational::Translator;
extend theories::relational::SMTInterface;

extend theories::integer::Translator;
extend theories::integer::SMTInterface;