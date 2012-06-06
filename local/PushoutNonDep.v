Add LoadPath "~/HoTT/HoTT/Coq".
Add LoadPath "~/HoTT/HoTT/local".

Require Import Homotopy CWComplexes FunExtFunctorial.

Set Implicit Arguments.

Section PushoutNonDep.

    Hypotheses A B C : Type.
    Hypotheses (f : A -> B) (g : A -> C).
    Hypothesis P : Type.
    
    Definition A_From_B : ( B -> P ) -> (A -> P) := fun x => compose x f.
    Definition A_From_C : ( C -> P ) -> (A -> P) := fun x => compose x g.
    
    Definition func_data := { bc : (B -> P) * (C -> P)
                              & (fst bc o f) == (snd bc o g) }.
    Lemma global_func_data : (pushout f g -> P) -> func_data.
    Proof.
        intros.
        exists ( X o po_from_b f g  , X o po_from_c f g ).
        simpl.
        apply (map (compose X)).
        apply pushout_cyl.
    Defined.
    
    Lemma funcDataAreGsd : func_data -> sect_data (fun p : pushout f g => P).
    Proof.
        intros.
        exists ( pr1 X ).
        assert ( h := pr2 X ).

        path_via (fst (pr1 X) o f).
        apply funext_dep; intro.
        apply trans_trivial.
    Defined.
    
    Lemma trivGsdAreFuncData : 
      sect_data (fun p : pushout f g => P) -> func_data.
    Proof.
        intros.
        exists (pr1 X).
        assert ( h := pr2 X ).
        simpl in h.

        apply (fun p => p @ h).
        apply funext_dep. intro a.
        unfold compose.
        apply opposite. apply trans_trivial.
    Defined.
    
    Lemma funcToSect_is_equiv : 
      sect_data (fun _ : pushout f g => P) <~> func_data.
    Proof.
        exists trivGsdAreFuncData.
        apply hequiv_is_equiv with funcDataAreGsd.
        
        intro.
        unfold funcDataAreGsd.
        unfold trivGsdAreFuncData.
        simpl.
        path_via ( (pr1 y ; pr2 y ) : func_data).
        moveright_onleft.
        apply concat2.
        apply funext_dep_opp. auto.
        destruct y. auto.
        
        intro.
        unfold funcDataAreGsd.
        unfold trivGsdAreFuncData at 1.
        simpl.
        path_via ( (pr1 x; pr2 x) : sect_data _ ).
        moveright_onleft.
        apply concat2.
        path_via ( ! ( ! funext_dep 
                       (fun a => ! trans_trivial (happly (pushout_cyl f g) a)
                                                 (fst (pr1 x) (f a))))).
        apply opposite. apply funext_dep_opp. auto.
        destruct x. auto.
    Defined.
    
    Lemma gfd_is_fd_of_sd : global_func_data 
      === trivGsdAreFuncData o (global_section_data (fun p : pushout f g => P)).
    Proof.
        intro F.
        apply opposite.
        unfold compose.
        unfold global_section_data.
        unfold trivGsdAreFuncData.
        simpl.
        unfold global_func_data.
        unfold compose.
        apply map.
        unfold either_way.
        moveright_onleft.
        assert ( h1 :=  funext_compute (fun ss : pushout f g -> P => 
        funext_dep (fun a : A => map_dep ss (happly (pushout_cyl f g) a)))
        F).
        fold funext in h1.
        apply (concat h1).
        moveleft_onright.
        path_via (funext_dep (fun a =>
        trans_trivial (happly (pushout_cyl f g) a) (F (po_from_b f g (f a))))).
        moveright_onleft.
        path_via ( funext_dep 
                    (fun a : A => happly_dep (! map (fun f0 x => F (f0 x))
                                            (pushout_cyl f g))
                    a)).
        set ( help := strong_funext_dep (F o po_from_c f g o g)
                                        (F o po_from_b f g o f)).
        set  ( h2 := inverse_is_retraction
                        (happly_dep (P := fun _ : A => P) ; help)).
        apply opposite.
        unfold help in h2.
        apply h2.
        moveleft_onleft.
        path_via ( funext_dep (fun a => 
        (map_dep F (happly (pushout_cyl f g) a)
        @ happly_dep (! map (fun f0 x => F (f0 x)) (pushout_cyl f g)) a))).
        apply opposite. apply funext_dep_distrib.
        apply funext_dep. intro.
        Focus 2. apply funext_dep_opp.
        set (Q := pushout_cyl f g ).
        fold (compose (po_from_b f g) f x).
        clear h1.
        induction Q. auto.
    Defined.
    
    Let raw_gfd_equiv := equiv_compose 
                           (global_section_data (fun _ : pushout f g => P); 
                              gsd_is_equiv (X := fun _ => P))
                              funcToSect_is_equiv.
    Lemma gfd_is_equiv : is_equiv global_func_data.
    Proof.
        apply (equiv_homotopic global_func_data _ gfd_is_fd_of_sd).
        assert (help := pr2 raw_gfd_equiv).
        unfold raw_gfd_equiv in help.
        unfold equiv_compose in help.
        simpl in help. auto.
    Defined.
    
    Definition gfd_equiv : equiv _ _ := (global_func_data ; gfd_is_equiv).
    
    Definition pushout_rec : 
      forall sd : func_data, pushout f g -> P
       := gfd_equiv ^-1.
    Definition pushout_triv_comps : 
      forall sd : func_data, global_func_data (pushout_rec sd) == sd
       := inverse_is_section gfd_equiv.
    
    Section PushoutTrivComps.
        
        Hypotheses ( ab : B -> P ) ( ac : C -> P )
          ( sh : ab o f == ac o g ).
        
        Let gf : func_data := ( ( ab, ac) ; sh ).
        Let grec := pushout_rec gf.
        Let rec_data := global_func_data grec.
        Let g_comps : rec_data == gf := pushout_triv_comps gf.
        
        Definition pushout_nd_comp_bc : pr1 rec_data == ( ab, ac )
          := (map pr1 g_comps).
        
        Definition pushout_nd_comp_b : fst (pr1 rec_data) == ab
          := (map (@fst _ _ ) pushout_nd_comp_bc).
        
        Definition pushout_nd_comp_c : snd (pr1 rec_data) == ac
          := (map (@snd _ _) pushout_nd_comp_bc).
        
        Definition pushout_nd_comp_cyl :
          ! (map A_From_B pushout_nd_comp_b) 
            @ (pr2 rec_data) 
            @ (map A_From_C pushout_nd_comp_c)
          == sh.
        Proof.
            set ( help := fiber_path g_comps ).
            set ( help2 := trans_paths _ _ (A_From_B o @fst _ _ )
                                           (A_From_C o @snd _ _ ) _ _ 
                                            pushout_nd_comp_bc 
                                            (pr2 rec_data) ).
            apply (fun p => p @ help ).
            apply (concat 
                     (y := (!map (A_From_B o @fst _ _ ) pushout_nd_comp_bc
                           @ pr2 rec_data) 
                           @ map (A_From_C o @snd _ _ ) pushout_nd_comp_bc)).
            apply concat2. apply concat2.
            apply (map opposite). unfold pushout_nd_comp_b. apply opposite.
            apply compose_map. auto.
            unfold pushout_nd_comp_c. apply opposite. apply compose_map.
            apply (concat (y := transport pushout_nd_comp_bc (pr2 rec_data))).
            exact (! help2). auto.
        Defined.
    
    End PushoutTrivComps.
End PushoutNonDep.