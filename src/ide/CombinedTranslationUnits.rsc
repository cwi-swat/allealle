module ide::CombinedTranslationUnits

import relational::Translator;
import relational::SMTInterface;

import integer::Translator;
import integer::SMTInterface;

import ModelFinder;

list[TranslationUnit] getTranslationUnits() = [<getRelationalTranslator(), getRelationalSMTInterface()>,<getIntTheoryTranslator(), getIntTheorySMTInterface()>];