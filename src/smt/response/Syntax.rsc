@license{
  Copyright (c) 2009-2015 CWI
  All rights reserved. This program and the accompanying materials
  are made available under the terms of the Eclipse Public License v1.0
  which accompanies this distribution, and is available at
  http://www.eclipse.org/legal/epl-v10.html
}
@doc{
	Synopsis: Grammar of the SMTLIBv2 response
}
@contributor{Jouke Stoel - stoel@cwi.nl (CWI)}

module lang::response::Syntax

extend lang::std::Layout;

start syntax Response
	= response: CheckSat sat
	| response: GetValue value
	| response: GetUnsatCore unsatCore
	| response: GetModel model
	;
	
syntax CheckSat 
	= sat: "sat" 
	| unsat: "unsat" 
	| unknown: "unknown"
	;
	
syntax GetUnsatCore = unsatCore: "(" Label* labels ")";

syntax GetValue = foundValues:"(" FoundValue* values ")";
syntax FoundValue = foundValue:"(" Expr var Expr val ")";

syntax GetModel = model:"(" "model" Command* interpretedFunctions ")";

syntax Command 
	= defineFunction:"(" "define-fun" Id name "(" SortedVar* params ")" Sort returnType Expr body")" 
	;

syntax SortedVar = sortedVar:"(" Id name Sort sort ")";

syntax Sort
	= \bool:"Bool"
	| \int:"Int"
	| custom: TypeId custom
	;
	
syntax Expr
	= lit: Literal lit
	//| wrappedExpr: "(" Expr expr ")"
	| var: Id varName
	| let: "(" "let" "(" Expr+ binding ")" Expr term ")"
	| cons:"(" Id constructor  Expr* exprs ")"
	| as:"(" "as" Id name Expr expr ")"
	;

syntax Literal
	= intVal:Int int
	| intVal: "(" Int int ")"
	| boolVal: Bool b
	;

lexical Int 
	//= [0-9]+ !>> [0-9]
	= [0-9]+ !>> [0-9]
	| [\-][\ ][0-9]+ !>> [0-9]
	;

lexical Bool = "true" | "false";
		
keyword Keywords = "true" | "false" | "let" | "as" | "Bool" | "Int";
		
lexical Id = ([a-z A-Z 0-9 _.] !<< [a-z A-Z][a-z A-Z 0-9 _.!]* !>> [a-z A-Z 0-9 _.]) \Keywords;
lexical Label = [a-z A-Z 0-9 _.$%|:/,?#\[\]] !<< [a-z A-Z 0-9 _.$%|:/,?#\[\]]* !>> [a-z A-Z 0-9 _.$%|:/,?#\[\]];
lexical TypeId = ([a-z A-Z 0-9 _.] !<< [A-Z][a-z A-Z 0-9 _.]* !>> [a-z A-Z 0-9 _.]) \Keywords;
