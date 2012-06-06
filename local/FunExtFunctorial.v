Add LoadPath "~/HoTT/HoTT/Coq".

Require Import Homotopy.

(** I found I needed these (intuitively obvious) functoriality results for
  [funext_dep] and friends.  Perhaps there's a more generic way to get the same
  results; I can't tell. It's the only immediate use of [inverse_is_retraction]
  I've run into outside Equivalences.v. *)

Section FunExtFunctorial.

    Hypotheses
      (A : Type)
      (P : A -> Type)
      (e f g : section P).
    
    Lemma funext_dep_distrib : 
      forall (h1 : e === f) ( h2 : f === g ),
        funext_dep ( fun a => h1 a @ h2 a )
         == (funext_dep h1) @ (funext_dep h2).
    Proof.
        intros.
        set (H1 := funext_dep h1).
        set (H2 := funext_dep h2).
        path_via (funext_dep (fun a => (happly_dep H1 a) @ (happly_dep H2 a))).
        apply funext_dep.
        intro.
        apply concat2.
        unfold H1. apply opposite. apply funext_dep_compute.
        apply opposite. apply funext_dep_compute.
        path_via ( funext_dep (fun a => happly_dep (H1 @ H2) a) ).
        apply funext_dep. intro.
        clearbody H1 H2. path_induction.
        apply (inverse_is_retraction
                  (@happly_dep A P e g ; strong_funext_dep e g )).
    Defined.
    
    Lemma funext_dep_opp :
      forall h1 : e === g,
        funext_dep h1 == ! funext_dep (fun a => ! h1 a).
    Proof.
        intro.
        set (H := funext_dep h1).
        path_via (! funext_dep (fun a => (!happly_dep H a))).
        path_via (! funext_dep (fun a => happly_dep (! H) a)).
        assert (help := inverse_is_retraction
                           (@happly_dep A P g e; strong_funext_dep g e)).
        simpl in help.
        path_via (! (! H)).
        apply (! help (! H)).
        apply funext_dep. intro. clearbody H. induction H.  auto.
        apply funext_dep. intro.
        unfold H. apply (map opposite).
        apply funext_dep_compute.
    Defined.
    
    Lemma funext_dep_idh : 
      funext_dep (fun a => idpath (f a)) == idpath f.
    Proof.
        path_via (funext_dep (fun a => happly_dep (idpath f) a)).
        assert (help := inverse_is_retraction
                           (@happly_dep A P f f; strong_funext_dep f f)
                           (idpath f)).
        simpl in help.
        unfold funext_dep.
        unfold strong_to_naive_funext_dep.
        auto.
    Defined.

End FunExtFunctorial.