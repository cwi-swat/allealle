module translation::theories::integer::tests::TesterBase

import logic::Integer;
import translation::theories::integer::Binder;

extend translation::tests::binderTests::TesterBase;

RelationMatrix truth(Index idx, Formula att) = (idx : relAndAtt(\true(), att));
RelationMatrix truths(map[Index, Formula] m) = (() | it + truth(i, m[i]) | i <- m);

RelationMatrix var(Index idx, str relName, Formula att) = (idx : relAndAtt(var("<relName>_<relVar(idx)>"), att));
RelationMatrix vars(map[Index,Formula] m, str relName) = (() | it + var(i,relName, m[i]) | i <- m);