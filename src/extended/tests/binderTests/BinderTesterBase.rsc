module extended::tests::binderTests::BinderTesterBase

extend orig::tests::binderTests::BinderTesterBase;

import extended::Binder;
import logic::Integer;

private Binding iV(Atom x, int i) = (<x>:\int(i));
