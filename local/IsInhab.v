Add LoadPath "../Coq".

Require Import Homotopy.

Close Scope nat_scope.


(** You can't squeeze anything into nothing *)
Definition IsEmpty ( X : Type ) : Type := X -> False. 

(** If you can't fit into nothing, you must have something, though perhaps
  we can't say what. *)
Definition is_inhab (X : Type ) := IsEmpty (IsEmpty X).

(** If we can, though, then vice-versa *)
Lemma inhab { X } : X -> is_inhab X.
  intros x f.
  contradict (f x).
Defined.

(** There's at most one way to not fit in nothing. We seem to need funext,
    but perhaps we should simply posit it? Do we not assume something
    equivalent in eta or some such? *)

Lemma is_conn_inhab { X : Type } : forall a b : is_inhab X, 
 a == b.
 intros.
 apply funext.
 intro.
 contradict (a x).
Defined.

(** wrapping the previous result in fancier terminology *)

Lemma if_inhab_then_inhab_contr { X : Type } :
 forall a : is_inhab X,
  is_contr (is_inhab X).
  intros.
  exists a.
  intros.
  apply is_conn_inhab.
Defined.

(** And so *)

Lemma is_inhab_is_prop (X : Type) : is_prop ( is_inhab X ).
  intro.
  intro.
  exists ( is_conn_inhab x y ).
  intros.
  refine ( contr_path2 _ _ (if_inhab_then_inhab_contr x)).
Defined.

(** This feels vaguely like cheating, but I'm quite sure
  there isn't any way around it. It's not as though I can
  apply funext or univalence to something that isn't a path or an
  equivalence. *)

Axiom is_inhab_ind : 
 forall (X : Type), is_prop X -> is_inhab X -> X.

Lemma prop_inhab_contr (X : Type) :
 is_prop X -> is_inhab X -> is_contr X.
 intros pr inh.
 exists (is_inhab_ind X pr inh).
 intros.
 apply pr.
Defined.

Lemma is_inhab_rect ( A : Type ) ( P : is_inhab A -> Type ) 
 ( dh : forall a, P (inhab a))
 (dp : forall (a b : is_inhab A)
  ( w : P a ) (z : P b) , transport (is_conn_inhab a b) w == z ) :
  forall (x : is_inhab A), P x.
 assert ( forall y , forall p q : P y, p == q ).
  intros.
  path_via (transport (is_conn_inhab y y) p).
 assert ( forall y : is_inhab A , is_prop (P y)).
  intro.
  intros p q. 
  exists ( X y p q ).
  intros. apply contr_path2.
  exists p.
  intro. apply ( X y ).
 assert ( forall y : is_inhab A, is_inhab (P y) ).
  intro.
  intro.
  apply y.
  intro.
  set ( a := inhab X2 ).
  set ( pp := is_conn_inhab a y ).
  set ( v := dh X2 ).
  fold a in v.
  assert ( z := transport pp v ).
  apply X1. exact z.
 intro.
 exact (is_inhab_ind (P x) (X0 x) (X1 x)).
Defined.

(** noodling around; some applications. *)

Fixpoint n_connected ( n : nat) : Type -> Type :=
 match n with
 | O => fun X => is_inhab X 
 | S m => fun X => is_inhab X * forall x y : X, n_connected m ( x == y ) end.

Definition component { X : Type } : X -> Type :=
 fun x => { y : X & is_inhab (x == y) }.

Definition components_are_subspaces { X : Type} ( x : X ) : component x -> X := 
 fun y => pr1 y.

Lemma fun_inhab { A B : Type } (f : A -> B ) :
 is_inhab A -> is_inhab B.
 intros.
 intro.
 apply X.
 exact ( X0 o f ).
Defined.

Lemma map_inhab { A B : Type } (f : A -> B ) 
 { a1 a2 : A } : is_inhab (a1 == a2) -> is_inhab ( f a1 == f a2 ).
 refine (fun_inhab _ ).
 intro.
 apply map.
 auto.
Defined.

Lemma inhab_contr_equiv ( X : Type ) :
 is_contr X -> is_equiv (@inhab X).
 intro.
 apply hequiv_is_equiv with (fun _ => (pr1 X0)).
 intro.
 assert ( H1 := if_inhab_then_inhab_contr y ).
 destruct H1 as [y0 pf].
 path_via y0.
 intro.
 destruct X0 as [ x0 pf ].
 refine (! pf _ ).
Defined.
