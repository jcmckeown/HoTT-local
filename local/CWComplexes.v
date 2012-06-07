Add LoadPath "../Coq".

Require Import Homotopy.

Set Implicit Arguments.

(* Jesse McKeown, Wednesday 23 May 2012
  While a PhD student in the Department of Mathematics
  at the University of Toronto *)

Section Sections.

  Hypothesis A : Type.
  Hypothesis P Q : A -> Type.
  Hypothesis f : section P -> section Q.
  Hypothesis s : section P.
  Hypothesis t : section Q.
  Hypothesis h k : f s == t.

  Lemma happly_htp_of_sectn : 
   forall hh : h == k,
    forall a : A,
    happly_dep h a == happly_dep k a.
    intro H. intro a.
    apply_happly.
    apply map.
    auto.
  Defined.

End Sections.

Section TransHomotopy.

  Hypothesis A B : Type.
  Hypothesis P : B -> Type.

   Hypothesis f g : A -> section P.
   Hypothesis x y : A.
  
  Section TQ.
  
   Hypothesis p : x == y.
   Hypothesis q : f x === g x.
   
   Definition tq : f y === g y.
    apply (transport (P := fun a => f a === g a) p).
    exact q.
   Defined.
   
   End TQ.

   Lemma trans_hpaths : 
    forall (p : x == y) (q : f x === g x) b,
     tq p q b == ! happly_dep (map f p) b @ q b @ happly_dep (map g p) b.
     intro p.
     intro q.
     intro b.
     unfold tq.
     induction p.
     simpl.
     set (w := q b).
     clearbody w.
     induction w. simpl. auto.
   Defined.

End TransHomotopy.

(**  Polymorphism over Set would allow us to define pushouts as the representing
  domain for maps from a disjoint union satisfying a parametrized family of
  equations. That is, *)

Definition polyMorphicNonDepPushout {A B C : Type} (f : A -> B) (g : A -> C)
 := forall (X : Type)(F : B -> X)(G : C -> X)(h : F o f == G o g), X.

  (** ... and that would work very well. so far as it goes, but Mike Shulman
  doubts one can prove dependent induction for these things. So we do the next-
  best thing. *)

Axiom pushout : forall { A B C : Type } (f : A -> B) (g : A -> C), Type.

Axiom pushout_ends : forall { A B C : Type } (f : A -> B) (g : A -> C),
 B + C -> pushout f g.

Definition po_from_b { A B C : Type} (f : A -> B)( g: A -> C) 
  := (pushout_ends f g) o (@inl B C).

Definition po_from_c { A B C : Type} (f : A -> B)( g: A -> C) 
 := (pushout_ends f g) o (@inr B C).

Axiom pushout_cyl : forall { A B C : Type } (f : A -> B) (g : A -> C),
 (po_from_b f g o f) == (po_from_c f g o g).

(** We have declared a space with two maps into it and some relations between
  them. The defining character of the pushout is that it's weakly-initial among
  such spaces-with-maps. *)

Section PushOutImplicitPolymorphism.

  Hypotheses A B C : Type.
  Hypotheses (f : A -> B) (g : A -> C).
  
  Let po := pushout f g.
  Let p_from_b := po_from_b f g.
  Let p_from_c := po_from_c f g.
  Let p_cyl := pushout_cyl f g.

  (** our by polymorphism we mean universalizing over dependent types over the
  assumed space po *)  

  Hypotheses X : po -> Type.

  Let GlobalSection := forall p : po, X p.
  Let BSection := section ( X o p_from_b ).
  Let CSection := section ( X o p_from_c ).

  (** Sections localize in various ways *)

  Let B_From_P : GlobalSection -> BSection.
   intros ss b.
   apply ss.
  Defined.
  Let C_From_P : GlobalSection -> CSection.
   intros ss c.
   apply ss.
  Defined.

  (** there ISN'T a canonical map from [A] to [po]; rather, there are too many *)

  Let ASection ( F : A -> po ) := section (X o F).
  Let ABSection := ASection (p_from_b o f).
  Let ACSection := ASection (p_from_c o g).

  (** more restriction maps *)

  Let AB_From_B : BSection -> ABSection.
   intros ss a. apply ss.
  Defined.
  Let AC_From_C : CSection -> ACSection.
   intros ss a. apply ss.
  Defined.

  (** There are two obvious ways to restrict from global sections down to [A];
    they are equivalent in a natural way. *)

  Let Compare_B_C : ABSection -> ACSection.
   intros ss a.
   assert ( path_in_po := happly p_cyl a).
   exact (transport (path_in_po) (ss a)).
  Defined.
  Let Compare_C_B : ACSection -> ABSection.
   intros ss a.
   exact (transport (happly (! p_cyl) a) (ss a)).
  Defined.
  
  (** This isn't used that I can think of, but it's reassuring,
   and surely someone else might want it. Might be rewritten using trans_is_equiv? *)

  Lemma Compare_is_equiv :
   is_equiv Compare_B_C.
   apply (hequiv_is_equiv Compare_B_C Compare_C_B).
   intro y.
   unfold Compare_B_C, Compare_C_B.
   apply funext_dep. intro a.
   path_via (transport (happly p_cyl a) (transport (! happly p_cyl a) (y a))).
    apply (map (fun pp => transport (A := po) pp (y a))).
    apply happly_opp.
   apply (trans_trans_opp (happly p_cyl a)).
   intro x.
   unfold Compare_B_C, Compare_C_B.
   apply funext_dep. intro a.
   path_via (transport (! happly p_cyl a) (transport (happly p_cyl a) (x a))).
    apply (map (fun pp => transport pp (transport (happly p_cyl a) (x a)))).
    apply happly_opp.
   apply (trans_opp_trans (happly p_cyl a)).
  Defined.

  (** This IS used, fairly-soon *)

  Lemma either_way : 
  Compare_B_C o AB_From_B o B_From_P == AC_From_C o C_From_P.
   apply funext. intro ss.
   apply funext_dep. intro a.
   unfold Compare_B_C.
   unfold compose.
   unfold AC_From_C, C_From_P, AB_From_B, B_From_P.
   apply map_dep.
  Defined.

  (** Abstraction: the idea Type of restricted data satisfying conditions *)

  Definition sect_data := 
  { bc : BSection * CSection &
       ( Compare_B_C o AB_From_B ) (fst bc) == AC_From_C (snd bc) }.

  (** And define a map of Types *)

  Definition global_section_data : GlobalSection -> sect_data
   := fun gs => ( ( B_From_P gs, C_From_P gs) ; (happly either_way gs)).
  
  (** The point of having a natural map from hypothetically-derived stuff
   to stuff we already knew about is that we can ask it be an equivalence. *)

  Axiom gsd_is_equiv : is_equiv global_section_data.
  
  Let pushout_equiv : GlobalSection <~> sect_data
   := (global_section_data ; gsd_is_equiv ).
  Definition pushout_rect := pushout_equiv ^-1.
  Definition pushout_comps : forall y : sect_data, global_section_data (pushout_rect y) == y
  := inverse_is_section pushout_equiv.

  (** OK, this doesn't need to be its own section, but it's sufficiently long
  ago since the last [Hypothesis], it seemed natural to add a layer of 
  referential locality *)

  Section POCompRules.
    
    Hypotheses (sb : BSection)
                      (sc : CSection)
                      ( sh : (Compare_B_C o AB_From_B) sb == AC_From_C sc).
    Let gs : sect_data := ( (sb, sc) ; sh ).
    
    Let gsr := pushout_rect gs.
    Let rect_data := global_section_data gsr.
    Let gs_comps := pushout_comps gs.
    
    Definition pushout_comp_bc : pr1 rect_data == ( sb, sc )
     := map pr1 gs_comps.
    Definition pushout_comp_b : fst (pr1 rect_data) == sb
     := map (@fst _ _) pushout_comp_bc.
    Definition pushout_comp_c : snd (pr1 rect_data) == sc
     := map (@snd _ _) pushout_comp_bc.
    
    Definition pushout_comp_cyl : transport pushout_comp_bc (pr2 rect_data) == sh
    := fiber_path gs_comps.

  End POCompRules.
  
  Section POPtCompRules.
     Definition psect_data := { bc : BSection * CSection & 
       forall a : A, transport (happly p_cyl a) (fst bc (f a)) == snd bc (g a) }.

     Lemma fibrMap : forall (bc : BSection * CSection), 
       ( Compare_B_C o AB_From_B ) (fst bc) == AC_From_C (snd  bc) ->
        forall a : A, transport (happly p_cyl a) (fst (idmap _ bc) (f a)) == snd (idmap _ bc) (g a).
       unfold idmap.
       intros bc sh.
       apply (happly_dep sh).
     Defined.
     
     Let tg := total_map 
        (Q := fun bc : BSection * CSection
          => forall a : A, transport (happly p_cyl a) (fst bc (f a)) == snd bc (g a))
       (idmap _ ) fibrMap .

     Lemma sect_psect_equiv : sect_data <~> psect_data.
       exists tg.
       apply total_is_equiv.
       intro.
       unfold fibrMap.
       apply strong_funext_dep.
     Defined.
     
     Definition pushout_pt_equiv : GlobalSection <~> psect_data :=
       equiv_compose pushout_equiv sect_psect_equiv.
     
     Definition pushout_pt_rect := pushout_pt_equiv ^-1.
     Definition pushout_pt_comps := inverse_is_section pushout_pt_equiv.
     
     Hypotheses (sb : BSection)
                       (sc : CSection)
                       ( ph : forall a : A, transport (happly p_cyl a) (sb (f a)) == sc (g a)).
     Let gpd : psect_data := ( (sb, sc) ; ph ).
     Let prect := pushout_pt_rect gpd.
     Let prect_data := tg (global_section_data prect).
     Let pr_comps := pushout_pt_comps ( (sb, sc); ph).
     
     Definition pushout_pt_comp_bc : pr1 ( prect_data ) == (sb, sc).
       exact (map pr1 pr_comps).
     Defined.
     Definition pushout_pt_comp_b : fst (pr1 prect_data) == sb.
       exact (map (@fst _ _ ) pushout_pt_comp_bc).
     Defined.
     Definition pushout_pt_comp_c : snd (pr1 prect_data) == sc.
       exact (map (@snd _ _) pushout_pt_comp_bc).
     Defined.
     
     Definition pushout_pt_comp_cyl : transport pushout_pt_comp_bc (pr2 (prect_data)) == ph := fiber_path pr_comps.
     
     Hypothesis a : A.
     
     Lemma explicit_ptwise_cyl :  ! map (transport (happly p_cyl a)) (happly_dep pushout_pt_comp_b (f a)) @ 
       map_dep prect (happly p_cyl a)
          == ph a @ ! (happly_dep pushout_pt_comp_c (g a)).
       moveleft_onright.
       set (help1 := happly_dep pushout_pt_comp_cyl a).
       apply (fun p => p @ help1 ).
       unfold fibrMap in tg.
       unfold total_map in tg.
       assert (help2 := trans_hpaths  (Compare_B_C o AB_From_B o @fst _ _) 
                                                    (AC_From_C o @snd _ _)
                      (pushout_pt_comp_bc)).
       simpl in help2.
       unfold idmap in help2.
       unfold tq in help2.
       set ( W := pr2 prect_data ).
       simpl in W.
       unfold Compare_B_C, AB_From_B, AC_From_C, compose in help2.
       simpl in help2.
       set ( help3 := help2 W a).
       unfold happly_dep in help3.
       unfold happly_dep.
       apply (fun p => p @ ! help3).
       unfold W.
       unfold pushout_pt_comp_b.
       unfold pushout_pt_comp_c.
       unfold happly_dep.
       
       assert ( map (fun h => h (g a)) (map (snd (B := CSection)) pushout_pt_comp_bc) ==
                  map (fun h => h a) (map (fun x a0 => snd x (g  a0)) pushout_pt_comp_bc ) ).
       undo_compose_map.
       apply (fun q => concat2 q X0).
       
       assert ( map (transport (happly p_cyl a)) 
                    (map (fun h => h (f a)) (map (fst (B := CSection)) pushout_pt_comp_bc)) ==
                  map (fun h => h a) (map (fun (x : BSection * CSection ) a0 => transport (happly p_cyl a0) (fst x (f a0))) pushout_pt_comp_bc) ).
       undo_compose_map.
       apply (concat2 (map opposite X1)).

       unfold either_way. simpl.
       
       assert ( help4 := funext_compute (fun ss : GlobalSection => 
                                                              funext_dep (fun a0 => map_dep ss (happly p_cyl a0))) prect).
       fold funext in help4.
       path_via (map (fun h : ACSection => h a) (funext_dep (fun a0 => map_dep prect (happly p_cyl a0)))).

       unfold ACSection. unfold ASection.
       path_via (happly_dep (funext_dep (fun a0 => map_dep prect (happly p_cyl a0))) a ).
       assert (help5 := funext_dep_compute (fun a0 => map_dep prect (happly p_cyl a0)) a).
       fold funext_dep in help5.
       simpl in help5.
       exact (! help5 ).
    Defined.
  End POPtCompRules.

End PushOutImplicitPolymorphism.

