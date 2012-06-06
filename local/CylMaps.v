Add LoadPath "~/HoTT/HoTT/Coq".
Add LoadPath "~/HoTT/HoTT/local".

Require Import Homotopy CWComplexes PushoutNonDep.

Set Implicit Arguments.

Local Arguments transport : default implicits.
Local Arguments map : default implicits.

Definition path_through { A : Type } { x y : A }
 ( p : x == y ) : forall w z : A, 
 ( w == x ) -> ( y == z ) -> ( w == z ).
 intros w z q r.
 exact ( q @ p @ r ).
Defined.

Section CylMaps.

  Hypotheses (A B C : Type) ( f : A -> B ) ( g : A -> C ).
  Hypotheses (Q R S : Type) ( h : Q -> R ) ( k : Q -> S ).

  Let Pfg := pushout f g.
  Let Phk := pushout h k.
  
  Hypotheses ( aq : A -> Q ) ( br : B -> R  ) ( cs : C -> S )
             ( hbr : br o f == h o aq ) ( hcs : cs o g == k o aq ).
  
  Let from_b : B -> Pfg := (po_from_b f g).
  Let from_c : C -> Pfg := (po_from_c f g).
  Let fg_cyl : from_b o f == from_c o g := pushout_cyl f g.
  Let pt_fg_cyl := happly fg_cyl.

  Let from_r : R -> Phk := (po_from_b h k).
  Let from_s : S -> Phk := (po_from_c h k).
  Let hk_cyl : from_r o h == from_s o k := pushout_cyl h k.
  Let pt_hk_cyl := happly hk_cyl.
  
  Lemma map_of_pushouts_data : func_data f g  Phk.
  exists (from_r o br, from_s o cs ).
  simpl.
  path_via ( from_r o h o aq ).
  apply (map (compose from_r)).
  exact hbr.
  path_via ( from_s o k o aq ).
  apply (map (fun x => x o aq)).
  apply pushout_cyl.
  apply (map (compose from_s)).
  exact (! hcs).
  Defined.

  Definition map_of_pushouts : Pfg -> Phk := pushout_rec map_of_pushouts_data.
  Let map_of_pushouts_rec_data := global_func_data map_of_pushouts.
  Definition map_of_pushouts_comps := pushout_triv_comps map_of_pushouts_data.
  
  Definition map_hbr_comp : map_of_pushouts o from_b == from_r o br :=
    map (@fst _ _) (map pr1 map_of_pushouts_comps).
  
  Definition map_hcs_comp : map_of_pushouts o from_c == from_s o cs :=
    map (@snd _ _) (map pr1 map_of_pushouts_comps).
  
  Definition map_of_pushouts_cyl_comp :
   transport (fun bc => fst bc o f == snd bc o g)
      (map pr1 map_of_pushouts_comps) (pr2 map_of_pushouts_rec_data)
   ==
   pr2 map_of_pushouts_data := fiber_path map_of_pushouts_comps.
  
  Definition map_of_pushouts_cylCat_comp :
    ! (map (fun bc => fst bc o f ) (map pr1 map_of_pushouts_comps)) @
      (pr2 map_of_pushouts_rec_data) @
      (map (fun bc => snd bc o g ) (map pr1 map_of_pushouts_comps)) ==
      pr2 map_of_pushouts_data.
  Proof.
    apply (path_through map_of_pushouts_cyl_comp); try auto.
    assert ( h2 := trans_paths ((B -> Phk) * (C -> Phk)) (A -> Phk)
                   (fun bc => fst bc o f)
                   (fun bc => snd bc o g)).
    apply opposite.
    unfold compose in h2.
    unfold compose.
    apply h2.
  Defined.

  Lemma m_o_p_ptwise_comp_cyl : forall a : A,
    !(happly map_hbr_comp (f a)) @ map (map_of_pushouts) (pt_fg_cyl a) @ (happly map_hcs_comp (g a))
  == 
    map from_r (happly hbr a)
         @
    (pt_hk_cyl (aq a))
         @
     ! map from_s (happly hcs a).
  Proof.
    intro.
    assert ( h1 := map (fun x => happly x a) map_of_pushouts_cylCat_comp).
    unfold compose in h1.
    unfold map_of_pushouts_data in h1.
    simpl projT2 in h1.
    unfold happly at 2 in h1.
    apply (path_through h1).
    unfold happly.
    do_concat_map.
    apply concat2.
    apply concat2.
    unfold map_hbr_comp.
     fold map_of_pushouts_data.
     fold Phk.
     set (PR := map pr1 map_of_pushouts_comps).
     unfold compose in PR. fold PR.
     clearbody PR.
     undo_compose_map.
     apply (concat (y :=
      ! map (fun h0 => h0 a) (map (fun bc x => fst bc (f x)) PR))).
     undo_compose_map. apply opposite.
     unfold compose.
     exact (opposite_map _ _ (fun h0 => h0 a) _ _
             (map (fun bc x => fst bc (f x)) PR) ).
     apply opposite.
     apply map_postcompose.
    unfold map_hcs_comp.
     fold map_of_pushouts_data.
     fold Phk.
      set (PR := map pr1 map_of_pushouts_comps).
      unfold compose in PR. fold PR.
     clearbody PR.
     undo_compose_map.
    do_concat_map.
    associate_right.
    apply concat2.
    undo_compose_map.
    unfold compose at 5. assert (w := map_postcompose _ _ from_r hbr a).
    apply (fun x => x @ w).
    unfold happly. undo_compose_map.
    apply concat2.
    unfold pt_hk_cyl. unfold hk_cyl.
    unfold happly.
    undo_compose_map.
    undo_compose_map.
    do_opposite_map.
    exact (opposite_map _ _ ((fun h0 => h0 a) o compose from_s) _ _ hcs).
    assert ( w := map_postcompose _ _ from_s hcs a).
    apply (fun x => x @ w).
    unfold happly. undo_compose_map.
  Defined.

End CylMaps.