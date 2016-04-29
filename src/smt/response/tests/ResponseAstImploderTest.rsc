module command::response::tests::ResponseAstImploderTest

import command::response::Imploder;
import command::response::Ast;

test bool withLet() =
	/GetModel model := toAst("(model (define-fun states () StateList (let ( (a!1 (true) )) a!1) ))");
	
test bool withNegativeInt() =
	/GetValue val := toAst("((s1 (consState (consCounter 4 (- 1) 1 2 1) noInitializeParams (consServeParams 4 1) noQueueParams)))");