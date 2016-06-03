module extended::tests::binderTests::BinderTesterBase

extend orig::tests::binderTests::BinderTesterBase;

import extended::Binder;
import logic::Integer;

private Binding iV(Atom x, int i) = (<x,intTheory()>:\int(i));
private Binding iV(Atom x) = (<x,intTheory()>:\var("<x>"));

private Binding iVal(Atom x, Formula f) = (<x, intTheory()>:f);
