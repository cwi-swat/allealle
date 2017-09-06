module ide::CombinedModelFinder

extend ModelFinder;

extend translation::theories::integer::Translator;
extend translation::theories::integer::SMTInterface;
extend translation::theories::integer::Unparser;

extend translation::theories::integerOpt::Translator;
extend translation::theories::integerOpt::SMTInterface;
extend translation::theories::integerOpt::Unparser;