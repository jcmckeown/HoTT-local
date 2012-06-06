HoTT-local
=========

This is a version of the main HoTT repository, tweaked to compile in Coq v. 8.4(β).  The most salient nifty feature
(bugs) in the latter include automatic η-conversion (so the Funext lemmata may not need to talk about eta,
eta_statement, &c.). In consequence, when I first ported, compiling would break because generated subgoals would resolve
too quickly!

There is also a subdirectoy local of HoTT including some (messy) work on axiomatizing homotopy pushouts and outlining
derived constructs such as suspensions, joins, and mapping telescopes, as well as my own take on the whole hequiv/hiso/
equiv family of equivalence types.

I hope it may be useful; if not, I hope it's not too ugly; if not... no need to tell me.