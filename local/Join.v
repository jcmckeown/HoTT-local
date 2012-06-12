Add LoadPath "../Coq".

Require Import Homotopy CWComplexes IsInhab.
Require Import MappingTelescope.

Section Join.

  Hypothesis A B : Type.
  
  Definition p1 := (@fst A B).
  Definition p2 := (@snd A B).
  
  Definition join := pushout p1 p2.
  
  Definition in_A := po_from_b p1 p2.
  Definition in_B := po_from_c p1 p2.

  Lemma join_joins_A_B : 
  forall a : A, forall b :B,
  in_A a == in_B b.
  intros.
  assert ( H := pushout_cyl p1 p2 ).
  exact ( happly H (a, b)).
  Defined.

  Lemma B_to_join_cone_A :
  forall a1 a2 : A, forall b : B,
  in_A a1 == in_A a2.
  intros.
  assert (H := pushout_cyl p1 p2 ).
  path_via (in_B b).
  exact (happly H (a1, b)).
  exact (!happly H (a2, b)).
  Defined.
  
  Lemma A_to_join_cone_B :
  forall a : A, forall b1 b2 : B,
  in_B b1 == in_B b2.
  assert (H := pushout_cyl p1 p2).
  intros.
  path_via (in_A a).
  exact (! happly H (a, b1)).
  exact (happly H (a, b2)).
  Defined.

End Join.


Lemma empty_join ( A B : Type ) :
    IsEmpty A -> IsEmpty B -> IsEmpty (join A B).
    intros.
    unfold IsEmpty.
    apply pushout_rect with ( X := fun x : join A B => False ).
    unfold sect_data.
    unfold compose.
    exists ( X , X0 ).
    simpl.
    apply funext_dep.
    intro.
    destruct x.
    contradict a.
    auto.
Defined.

Lemma inhabited_join ( A B : Type ):
    IsEmpty B -> is_inhab (join A B) -> is_inhab A.
    intros.
    intro.
    assert ( W := empty_join A B X1 X).
    apply X0.
    auto.
Defined.
