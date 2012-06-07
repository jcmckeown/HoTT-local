Add LoadPath "../Coq".

Require Import Homotopy.

Close Scope nat_scope.

Definition IsEmpty ( X : Type ) : Type := X -> False.

Definition is_inhab (X : Type ) := IsEmpty (IsEmpty X).

Lemma is_conn_inhab { X : Type } : forall a b : is_inhab X, 
 a == b.
 intros.
 apply funext.
 intro.
 contradict (a x).
Defined.

Lemma if_inhab_then_inhab_contr { X : Type } :
 forall a : is_inhab X,
  is_contr (is_inhab X).
  intros.
  exists a.
  intros.
  apply is_conn_inhab.
Defined.

Lemma is_inhab_is_prop (X : Type) : is_prop ( is_inhab X ).
  intro.
  intro.
  exists ( is_conn_inhab x y ).
  intros.
  refine ( contr_path2 _ _ (if_inhab_then_inhab_contr x)).
Defined.

Fixpoint n_connected ( n : nat) : Type -> Type :=
 match n with
 | O => fun X => is_inhab X 
 | S m => fun X => is_inhab X * forall x y : X, (n_connected m ( x == y )) end.

(** The definition above proposes 0-connected for inhabited,
1-connected for inhabited path-connected, 2-connected for path-simply-path-connected
spaces, etc. I suppose every space is (-1)-connected? *)

Definition component { X : Type } : X -> Type :=
 fun x => { y : X & is_inhab (x == y) }.

Definition components_are_subspaces { X : Type} ( x : X ) : component x -> X := 
 fun y => pr1 y.

(** There is a monad structure one can write on is_inhab --- it's basically 
    because IsEmpty is a corepresentable endofunctor?
 *)