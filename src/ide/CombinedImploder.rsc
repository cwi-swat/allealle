module ide::CombinedImploder

import ide::CombinedSyntax;
import ide::CombinedAST;
import ide::Parser;
import ide::CombinedDomainResolver;

extend translation::Imploder;
extend translation::theories::integer::Imploder;
extend translation::theories::integerOpt::Imploder;

import ParseTree;
import IO;

ide::CombinedAST::Problem implodeProblem(loc file)         = implodeProblem(parseFile(file).top);
ide::CombinedAST::Problem implodeProblem(loc file, str x)  = implodeProblem(parseFile(x, file).top);
ide::CombinedAST::Problem implodeProblem(str x)            = implodeProblem(parseString(x).top);

ide::CombinedAST::Problem implodeProblem(ide::CombinedSyntax::Problem p) {
  ResolvedDomains dom = resolveDomains(p);
  return implodeProblem(p,dom);  
}