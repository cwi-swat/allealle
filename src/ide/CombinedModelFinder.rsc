module ide::CombinedModelFinder

extend ModelFinder;

extend theories::integer::PreProcessor; 
extend theories::integer::Translator;
extend theories::integer::SMTInterface;