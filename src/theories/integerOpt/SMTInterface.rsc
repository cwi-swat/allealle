module theories::integerOpt::SMTInterface

extend theories::integer::SMTInterface;

str compile(minimize(Formula f)) = "(minimize <compile(f)>)";
str compile(maximize(Formula f)) = "(maximize <compile(f)>)";
