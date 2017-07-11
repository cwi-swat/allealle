module ide::CombinedModelFinder

extend ModelFinder;

extend theories::integer::PreProcessor; 
extend theories::integer::Translator;
extend theories::integer::SMTInterface;
extend theories::integer::Unparser;

extend theories::integerOpt::PreProcessor; 
extend theories::integerOpt::Translator;
extend theories::integerOpt::SMTInterface;
extend theories::integerOpt::Unparser;