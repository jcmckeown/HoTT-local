Add LoadPath "../Coq".

Require Import Homotopy CWComplexes CylMaps.

Section MapTelescope.

 Definition mapSeq := { Xs : nat -> Type & forall n, Xs n -> Xs (S n) }.
 Hypothesis MS : mapSeq.
 Definition UM := { n : nat & (pr1 MS) n }.

 Let UShift : UM -> UM.
  intro.
  destruct X as [n x].
  exists (S n).
  apply ( (pr2 MS n) ).
  exact x.
 Defined.
 
 Definition TwoUM := sum UM UM.
 
 Definition layer : TwoUM -> UM :=
 fun u =>
 match u with
 | inr v => v
 | inl v => v end.
 
 Definition tshift : TwoUM -> UM :=
 fun u =>
 match u with
 | inr v => UShift v
 | inl v => v end.
 
 Definition MT :=
  pushout layer tshift.
 
 Fixpoint map_down_k (k : nat) : UM -> UM :=
  match k with 
  | O => idmap _ 
  | S l => UShift o map_down_k l end.
 
 Definition base_inc : UM -> MT :=
  po_from_b layer tshift.
  
 Lemma collapse_scope : forall (k : nat),
  forall x : UM, 
  base_inc x == base_inc (map_down_k k x).
  intro k.
  induction k.
  intros.
  simpl. auto.
  intros.
  apply @concat with  (y:= base_inc (map_down_k k x)).
  apply (IHk x).
  assert (PTH := happly (pushout_cyl layer tshift) (inr (map_down_k k x))).
  unfold compose in PTH.
  apply (concat PTH).
  unfold base_inc.
  assert (QTH := happly (pushout_cyl layer tshift) (inl (map_down_k (S k) x))).
  simpl.
  simpl in QTH.
  apply opposite.
  auto.
 Defined.

End MapTelescope.

Section AUsefulEquivalence.

 Hypothesis MS : mapSeq.
 Definition OneTrunc : mapSeq.
 exists ( fun n => (pr1 MS) (S n)).
  intros.
  apply (pr2 MS (S n)).
  auto.
 Defined.
 
 Section MSToOT.
 
     Let AQ : TwoUM MS -> TwoUM OneTrunc.
     Proof.
         intro.
         remember X as Y.
         destruct Y.
         apply inl.
         destruct u.
         exists x.
         unfold OneTrunc.
         simpl.
         apply (pr2 MS x).
         auto.
         apply inr.
         destruct u.
         exists x.
         unfold OneTrunc.
         simpl.
         apply (pr2 MS x).
         auto.
     Defined.
     
     Let BR : UM MS -> UM OneTrunc.
     Proof.
         intro.
         destruct X.
         exists x.
         apply  (pr2 MS x).
         auto.
     Defined.

     Lemma include_again : (MT MS) -> (MT OneTrunc).
       apply @map_of_pushouts with (aq := AQ) (br := BR) (cs := BR);
       apply funext; intro u; destruct u as [ [ a b ] | [ a b ]] ; auto.
     Defined.
     
 End MSToOT.
 
 Section OTToMS.
   
   Let BR : UM OneTrunc -> UM MS.
     intro.
     destruct X.
     exists (S x).
     auto.
   Defined.
   
   
   Let AQ : TwoUM OneTrunc -> TwoUM MS :=
    fun v => 
    match v with
    | inl w => inl (BR w)
    | inr w => inr (BR w) end.
   
   Lemma include_from : (MT OneTrunc) -> (MT MS).
      apply @map_of_pushouts with (aq := AQ) (br := BR) (cs := BR);
      apply funext; intro u; destruct u as [ [ a b ] | [ a b ]] ; auto.
   Defined.

 End OTToMS.

(* 
 Lemma MT_OT_equiv : (MT MS) <~> (MT OneTrunc).
   exists include_again.
   apply hequiv_is_equiv with include_from.
   intros.
   apply pushout_rect with ( X := fun z => include_again (include_from z) == z ).
   unfold sect_data.
    unfold compose.
    
*)

End AUsefulEquivalence.