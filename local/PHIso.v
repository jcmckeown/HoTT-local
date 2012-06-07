Add LoadPath "~/HoTT/HoTT/Coq".

Require Import Contractible.

Close Scope nat_scope.

Definition pr20 { A } { P : A -> Type } { Q : A -> Type } : sigT2 P Q -> A.
  intro x.
  destruct x; auto.
Defined.

Definition pr21 { A } { P : A -> Type } { Q : A -> Type } : forall x : sigT2 P Q, P (pr20 x).
  intro x.
  destruct x; auto.
Defined.

Definition pr22 { A } { P : A -> Type } { Q : A -> Type } : forall x : sigT2 P Q, Q (pr20 x).
  intro x.
  destruct x; auto.
Defined.

Notation " ( a ; b ; c ) " := (existT2 _ _ a b c).

Definition esopmoc { A B C : Type } (f : A -> B) (g : B -> C) : A -> C :=
 fun a => g ( f a ).

Lemma composescommute { A B C D : Type } (f : A -> B) (g : B -> C) (h : C -> D) :
 esopmoc f (compose h g) == compose h (esopmoc f g).
 auto.
Defined.

Notation " f *~ p " := (map (compose f) p) (at level 76, right associativity).
Notation " p ~| g " := (map (esopmoc g) p) (at level 74, left associativity).

Lemma push_or_pull { A B C D : Type } (f : C -> D) (g h : B -> C) (k : A -> B)
 (p : g == h) :
 (( f *~ p ) ~| k) == (f *~ ( p ~| k )).
 undo_compose_map.
Defined.

Ltac push_pull_assoc :=
 match goal with
 | |- context cxt[(?f *~ ?p) ~| ?g] =>
  let mid := context cxt[ f *~ ( p ~| g) ] in
  path_using mid push_or_pull end.

Lemma comp_nat { X Y : Type } : forall f g : X -> Y, 
    forall x y : X,
    forall p : x == y,
    forall q : f == g,
    map f p @ happly q y == happly q x @ map g p.
    Proof.
        path_induction.
    Defined.

Section PHIso.

    Hypotheses ( A B : Type ).
    Definition p_sect { X Y : Type } ( f : X -> Y ) (g : Y -> X) := f o g == idmap Y.
    
    Definition p_iso := { f : A -> B & { g : B -> A & p_sect f g & { h : A -> B & p_sect g h } } }.
    
    Definition p_equiv := { f : A -> B & is_contr { g : B -> A & p_sect f g } }.
    
    Lemma comp_assoc : forall f h : A -> B, forall g : B -> A, 
        f o ( g o h ) == (f o g) o h.
        intros.
        unfold compose.
        auto.
    Defined.
    
    Section Naturalities.
    
        Hypotheses ( Y Z : Type) (g : Y -> Z) (h : Z -> Y) (r : p_sect g h).
        
        Lemma sect_nat : forall (X : Type) ( x y : X -> Z ) ( p : x == y ),
          map (esopmoc x) r @ p == map (compose (g o h)) p @ map (esopmoc y) r.
        Proof.
            induction p.
            cancel_units.
        Defined.
        
        Lemma sect_conat : forall ( W : Type) ( x y : Z -> W ) (p : x == y),
          map (compose x) r @ p == map (esopmoc ( g o h )) p @ map (compose y) r.
          path_induction.
          cancel_units.
        Defined.
        
        Lemma sect_absb : forall (X : Type) (x : X -> Z),
          (r ~| (g o h o x)) == ((g o h) *~ r ~| x).
        Proof.
            intros.
            apply @concat_cancel_right with (r := r ~| x).
            apply sect_nat.
        Defined.
    
    End Naturalities.

    Section AssumePIso.
    
        Hypothesis H : p_iso.
        
        Lemma p_iso_to_p_equiv : p_equiv.
        Proof.
            remember H as HH.
            destruct HH as [ h [ f R [ g S ]]].
            unfold p_sect in *.
            exists h.
            exists (f ; R).
            set ( g_is_h := ! ( R ~| g ) @ (h *~ S) : g == h).
            intro.
            destruct y as [ f' R' ].
            apply total_path with (! (S ~| f')
                              @ ( f *~ g_is_h ~| f' )
                               @ (f *~ R') ).
            simpl.
            refine ((trans_paths _ _ (compose h) (fun _ : B -> A => idmap B) _ _
                          (! ( S ~| f') @ ( f *~ g_is_h ~| f' ) @ (f *~ R')) _) @ _). 
            cancel_units.
            do_concat_map.
            do_opposite_map.
            moveright_onleft.
            associate_right.
            moveleft_onleft.
            unfold g_is_h.
            do_concat_map.
            associate_right.
            moveleft_onleft.
            do_opposite_map.
            path_via ( ( R ~| h o f o g o f' ) @ ( h *~ S ~| f' ) @ R' ).
            associate_left.
            refine ( _ @ ! (sect_absb _ _ _ _ R _ (g o f') ) @ _ ).
            undo_compose_map. auto.
            undo_concat_map.
            associate_left.
            refine ( _ @ sect_nat _ _ _ _ R _ _ _ (( h *~ S ~| f') @ R') @ _ ).
            do_concat_map.
            undo_compose_map.
            unfold compose, esopmoc. associate_right.
            do_concat_map.
            undo_compose_map.
            apply idmap_map.
        Defined.
    
    End AssumePIso.

End PHIso.