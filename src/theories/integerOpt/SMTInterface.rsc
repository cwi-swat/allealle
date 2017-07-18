module theories::integerOpt::SMTInterface

extend theories::integer::SMTInterface;

str compileCommand(minimize(Formula f)) = "(minimize <compile(f)>)";
str compileCommand(maximize(Formula f)) = "(maximize <compile(f)>)";
