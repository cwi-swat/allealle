module smtlogic::core::BasicRewriteRules

import smtlogic::core::CoreTerms;

Formula \or({\false(), *Formula r})  = \or(r);
Formula \or({\true(), *Formula _})   = \true();
Formula \or(\true(), Formula _)			 = \true();
Formula \or(Formula _, \true())			 = \true();

Formula \and({\true(), *Formula r})  = \and(r);
Formula \and({\false(), *Formula _}) = \false();
Formula \and(\false(), Formula _)		 = \false();
Formula \and(Formula _, \false())		 = \false();
