module ide::CombinedModelFinder

extend ModelFinder;

extend theories::integer::Translator;
extend theories::integer::SMTInterface;
extend theories::integer::Unparser;

extend theories::integerOpt::Translator;
extend theories::integerOpt::SMTInterface;
extend theories::integerOpt::Unparser;