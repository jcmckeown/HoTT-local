Add LoadPath "../Coq".

Require Import Contractible.

Close Scope nat_scope.

Set Implicit Arguments.

Local Notation " f === g " := (forall x, f x == g x) (at level 62).

Definition pr20 { A } { P : A -> Type } { Q : A -> Type } : sigT2 P Q -> A.
  intro x.
  destruct x; auto.
Defined.

Definition pr21 { A } { P : A -> Type } { Q : A -> Type } :
  forall x : sigT2 P Q, P (pr20 x).
Proof.
    intro x.
    destruct x; auto.
Defined.

Definition pr22 { A } { P : A -> Type } { Q : A -> Type } : 
  forall x : sigT2 P Q, Q (pr20 x).
Proof.
    intro x.
    destruct x; auto.
Defined.

Notation " ( a ; b ; c ) " := (existT2 _ _ a b c).

Definition is_sect { A B : Type } (f : A -> B) ( g : B -> A )
 := forall a, f (g a) == a.


Section HIso.

    Hypotheses (A B : Type) (f : A -> B).
    
    Definition is_equiv := forall b : B, is_contr ( hfiber f b ).
    
    Definition is_hiso : Type := 
     { g : B -> A & is_sect f g & { h : A -> B & is_sect g h }}.
    
    Section HIsos.
    
        Hypotheses g : B -> A.
        Hypotheses h : A -> B.
        Hypotheses sect : is_sect f g.
        Hypotheses retr : is_sect g h.
        
        Definition mk_iso : is_hiso := ( g ; sect ; ( h ; retr )).
        
        Lemma same_obverse : forall a, f a == h a.
        Proof.
            intro. unfold is_sect in sect.
            path_via (f ( g (h a))).
        Defined.
        
        Lemma same_obv_nat : forall x y, forall p : x == y,
            map f p @ same_obverse y == same_obverse x @ map h p.
            intros.
            induction p.
            cancel_units.
        Defined.

        Lemma sect_natural :
          forall x y, forall p : x == y, sect x @ p == map f (map g p) @ sect y.
        Proof.
            intros.
            induction p.
            cancel_units.
        Defined.
        
        Lemma sect_absb : forall x, sect (f (g x)) == map f (map g (sect x)).
            intros.
            apply @concat_cancel_right with (r := sect x).
            apply sect_natural.
        Defined.
        
        (** Coq's automatic parameter detection, in the end, doesn't distinguish
            the next two lemmata from the previous two; they differ locally, though
            in that the local instances refer to distinct local parameters. *)

        Lemma retr_natural : 
          forall x y, forall q : x == y, retr x @ q == map g (map h q) @ retr y.
        Proof.
            intros.
            induction q.
            cancel_units.
        Defined.
        
        Lemma retr_absb : forall x, retr (g (h x)) == map g (map h (retr x)).
        Proof.
            intro.
            apply @concat_cancel_right with (r := retr x).
            apply retr_natural.
        Defined.
    
    End HIsos.
    
    Definition is_hequiv := { g : B -> A & is_sect f g & is_sect g f }.
    
    (** These really aren't needed *)
    (*
    Section IsoVsHequiv.
    
        Lemma is_hiso_to_is_hequiv : is_hiso -> is_hequiv.
        Proof.
            intro H.
            destruct H as [ g s [h r] ].
            exists g.
            auto.
            intro.
            path_via (g (h a)).
            apply @same_obverse with g; auto.
        Defined.
        
        Lemma is_hequiv_to_is_hiso : is_hequiv -> is_hiso.
        Proof.
            intro.
            destruct X as [g  p q ].
            exists g; auto.
            exists f; auto.
        Defined.
        
    End IsoVsHequiv.
    *)
End HIso.

Section HIsoCompose.

    Hypotheses A B C : Type.
    Hypotheses (f : A -> B) ( g : B -> C).
    
    Section Compose.
    
        Hypotheses hf : is_hiso f.
        Hypotheses hg : is_hiso g.
        
        Lemma compose_hiso : is_hiso (g o f).
        Proof.
            remember hf as Hf.
            destruct Hf as [ g1 s1 [ g2 s2 ]].
            remember hg as Hg.
            destruct Hg as [ h1 r1 [ h2 r2 ]].
            exists ( g1 o h1 ).
            intro.
              path_via (g (h1 a)).
              unfold compose. apply map.
              apply s1.
            exists ( h2 o g2 ).
            intro.
              path_via (g1 (g2 a)).
              unfold compose.
              apply map.
              apply r2.
        Defined.
    
    End Compose.
    
    Section Cancel.
    
        Hypotheses hgf : is_hiso (g o f).
        
        Section CancelRight.
        
            Hypotheses hf : is_hiso f.
            Lemma cancel_right_hiso : is_hiso g.
            Proof.
                remember hgf as Hgf.
                destruct Hgf as [ Lgf s [ Rgf r ]].
                remember hf as Hf.
                destruct Hf as [ Lf u [ Rf v ]].
                exists ( f o Lgf ).
                intro.
                path_via ( (g o f) (Lgf a)).
                exists ( Rgf o Lf ).
                intro.
                path_via ( f (Lf a)).
                unfold compose.
                apply map.
                apply r.
            Defined.
        
        End CancelRight.
        
        (** This is the tricky one. It makes much more sense in pasting figures *)
        
        Section CancelLeft.
        
            Hypotheses hg : is_hiso g.
            Lemma cancel_left_hiso : is_hiso f.
            Proof.
                remember hgf as Hgf.
                destruct Hgf as [ Lgf s [ Rgf r ]].
                remember hg as Hg.
                destruct Hg as [ Lg u [ Rg v ]].
                exists ( Lgf o g ).
                intro.
                path_via (Lg (g ( f ( Lgf (g a))))).
                path_via (Lg (Rg (f (Lgf (g a))))).
                refine (! same_obverse u v _).
                path_via (Lg ((g o f) (Lgf (g a)))).
                path_via (Lg (g a)).
                path_via (Lg (Rg a)).
                refine ( same_obverse u v _ ).
                exists f.
                intro.
                path_via (Lgf ( (g o f) a)).
                path_via ( Lgf ( Rgf a )).
                refine ( same_obverse s r _ ).
            Defined.
        End CancelLeft.
    
    End Cancel.

End HIsoCompose.

Section HIsEquiv.

    Hypotheses (A B : Type)
     (f : A -> B) ( W : is_hiso f ).
    
    Lemma h_is_equiv : 
     is_equiv f.
     remember W as V.
     destruct V as [ g s [ h r ]].
     set ( R := same_obverse s r ).
     intro a.
     exists ( g a ; s a ).
     intro.
     destruct y as [ b p ].
     apply total_path with (! r b @ ! map g (R b) @ map g p ).
     path_via (! map f (! r b @ ! map g (R b) @ map g p) @ p ).
     refine ((trans_paths A B f (fun _ => a) _ _ 
              ( ! r b @ ! map g (R b) @ map g p )  p ) @ _ ).
     cancel_units.
     unfold R.
     do_concat_map.
     do_opposite_map.
     moveright_onleft.
     associate_right.
     moveleft_onleft.
     moveleft_onleft.
     unfold same_obverse.
     do_concat_map.
     do_opposite_map.
     associate_right.
     moveright_onleft.
     path_via (s (f (g (h b))) @ (map f (r b) @ p)).
     apply opposite.

       apply sect_absb.

     path_via (map f (map g (map f (r b) @ p)) @ s a).

       apply sect_natural.

     do_concat_map.
     associate_left.
   Defined.

End HIsEquiv.