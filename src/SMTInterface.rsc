module SMTInterface

import AST;
import Binder;
import logic::Boolean;

alias Model = map[SMTVar, Formula];

alias SMTVar = tuple[str name, Theory theory];

alias SMTVarCollector = set[SMTVar] (Environment);
alias SMTCompiler = tuple[str (SMTVar) declareVariable, str (Formula, str (Formula)) compile]; 
alias SMTInterpreter = tuple[Model (map[str,str], set[SMTVar]) getValues, Environment (Model, Environment) merge, str (SMTVar, Model) variableNegator];

alias SMTInterface = tuple[SMTVarCollector collectVars, SMTCompiler compiler, SMTInterpreter interpreter]; 