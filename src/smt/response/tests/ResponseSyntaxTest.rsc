module command::response::tests::ResponseSyntaxTest

import command::response::Parser;
import command::response::Syntax;

test bool basic() = 
	/GetModel model := parseResponse("(model (define-fun test () Bool true))"); 

test bool withLet() =
	/GetModel model := parseResponse("(model (define-fun states () StateList (let ( (a!1 (true) ) true) )))");
	
test bool withNegativeInt() =
	/GetValue val := parseResponse("((s1 (consState (consCounter 4 (- 1) 1 2 1) noInitializeParams (consServeParams 4 1) noQueueParams)))");