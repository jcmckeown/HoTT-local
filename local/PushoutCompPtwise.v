Add LoadPath "~/HoTT/HoTT/Coq".

Require Import Homotopy CWComplexes.

Section PtWiseComps.

  Hypotheses A B C : Type.
  Hypotheses (f : A -> B) (g : A -> C).

  Let Ph := pushout f g.

  Hypotheses X : Ph -> Type.

  Let p_from_b := po_from_b f g.
  Let p_from_c := po_from_c f g.
  Let p_cyl := pushout_cyl f g.

  (** our by polymorphism we mean universalizing over dependent types over the
  assumed space po *)  

  Let GlobalSection := section X.
  Let BSection := section ( X o p_from_b ).
  Let CSection := section ( X o p_from_c ).

  Let ASection ( F : A -> Ph ) := section (X o F).
  Let ABSection := ASection (p_from_b o f).
  Let ACSection := ASection (p_from_c o g).

(* Compare_B_C was
  fun (ss : section (X o (po_from_b f g o f))) (a : A) => transport (happly (pushout_cyl f g) a) (ss a))
  We only ever want it applied to stuff, which is why it's not exported as its own thing...
  
  AB_From_B would be (compose _ f) except it's the wrong type for compose.
  anyway the composites we always wanted are
  fun a => transport (happly (pushout_cyl f g) a) (sb (f a)) === fun a => (sc (g a)) *)
  
  Hypotheses (sb : BSection)
                    (sc : CSection)
                    (sh : forall a : A,
                      transport (happly (pushout_cyl f g) a) (sb (f a)) == (sc (g a))).
  Let sh_h := funext_dep sh.
  
  Definition ptwisePushoutRect := pushout_rect ((sb, sc); sh_h).
  Definition ptwisePushoutData := global_section_data _ ( ptwisePushoutRect ).
  Definition ptwisePushoutComps := pushout_comps ((sb, sc); sh_h).
  
  Lemma ptwiseCompB : forall b : B, ptwisePushoutRect (po_from_b f g b) == sb b.
    intro.
    set (help := (map (@fst _ _ o pr1) ptwisePushoutComps )).
    apply (happly_dep help).
  Defined.
  Lemma ptwiseCompC : forall c : C, ptwisePushoutRect (po_from_c f g c) == sc c.
    intro.
    set (help := (map (@snd _ _ o pr1) ptwisePushoutComps )).
    apply (happly_dep help).
  Defined.
  Lemma ptwiseCompCyl1 : forall a0 : A,
    happly_dep (transport (map pr1 ptwisePushoutComps) (pr2 ptwisePushoutData)) a0 == sh a0.
    assert (h1 := pushout_comp_cyl sh_h).
    unfold ptwisePushoutData.
    unfold ptwisePushoutRect.
    intro.
    apply (concat (y := happly_dep sh_h a0)).
    assert (h2 := map_dep (fun x => happly_dep x a0) h1).
    simpl in h2.
    apply (fun x => x @ h2).
    apply opposite.
    apply trans_trivial.
    unfold sh_h.
    apply (funext_dep_compute sh).
  Defined.

  Hypothesis α : A.
  
  Lemma ptwiseCompCyl : ! map (transport (happly (pushout_cyl f g) α)) (ptwiseCompB (f α)) @ 
     map_dep (ptwisePushoutRect) (happly (pushout_cyl f g) α)
         == sh α @ ! (ptwiseCompC (g α)).
     assert ( h1 := ptwiseCompCyl1 α ).
     Local Arguments transport { A } P { x y } p X.
     set ( h2 := trans_paths (( section (X o po_from_b f g )) * (section (X o po_from_c f g)))
                    ( section (X o po_from_c f g o g )) 
                    (fun bc x => transport X (happly (pushout_cyl f g) x) (fst bc (f x)))
            (fun bc x => (snd bc (g x))) _ _ (map pr1 ptwisePushoutComps) 
             (pr2 (global_section_data _ ptwisePushoutRect))).
     unfold happly_dep in h1.
     unfold compose in h1.
     unfold compose in h2.
     simpl in h2.
     moveleft_onright.
     apply (fun x => x @ h1 ).
     assert (h3 := map (fun x => happly_dep x α) h2).
     simpl in h3.
     unfold happly_dep at 1 in h3.
     unfold ptwisePushoutData.
     unfold global_section_data. simpl.
     apply ( fun x => x @ ! h3 ).
     unfold happly_dep.
     do_concat_map. clear h1 h2 h3.
     unfold ptwiseCompC.
     unfold happly_dep.
     unfold compose.
     apply concat2.
     moveright_onleft.
     unfold happly.
     Focus 2.
     undo_compose_map.
     undo_compose_map.
     unfold ptwiseCompB.
     moveleft_onleft.
     do_opposite_map.
     apply concat2.
     apply (map opposite).
     unfold happly_dep.
     undo_compose_map.
     Focus 2. 
     apply opposite.
     exact (opposite_map _ _ (fun h : section (X o po_from_c f g o g) => h α) _ _ _ ).
     unfold either_way.
     do_compose_map.
     apply (concat ( y := 
       map (fun h : forall x : A, X (po_from_c f g (g x)) => h α)
        (happly (funext (fun ss : forall p : pushout f g , X p => 
          funext_dep (fun a => map_dep ss (happly (pushout_cyl f g) a)))) ptwisePushoutRect))).
     apply (concat ( y := 
       map (fun h : forall x : A, X (po_from_c f g ( g x)) => h α)
        (funext_dep (fun a : A => map_dep ptwisePushoutRect (happly (pushout_cyl f g) a))))).
     apply (concat ( y :=
      happly_dep (funext_dep (fun a => map_dep ptwisePushoutRect (happly (pushout_cyl f g) a))) α)).
     assert ( W := funext_dep_compute (fun a : A => map_dep ptwisePushoutRect 
                                     (happly (pushout_cyl f g) a)) α).
     fold funext_dep in W. simpl in W.
     apply (fun x => x @ !W).
     unfold happly. auto.
     unfold happly_dep. auto.
     apply map. apply opposite.
     exact ( funext_compute (fun ss : section X => funext_dep (fun a => map_dep ss
                     (happly (pushout_cyl f g) a))) ptwisePushoutRect).
     unfold happly. auto.
   Defined.

End PtWiseComps.