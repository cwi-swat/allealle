module translation::theories::integerOpt::SMTInterface

extend translation::theories::integer::SMTInterface;

str compileCommand(minimize(Formula f)) = "(minimize <compile(f)>)";
str compileCommand(maximize(Formula f)) = "(maximize <compile(f)>)";
