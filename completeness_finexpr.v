Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools algebra Bool relations pomsets.
Require Import finite_expr finexp_pomsets.
Require Import bsp_terms bsp_pomsets.

Section s.
  Context {X : Set}.  
  (** * Finite languages *)
  Definition ℒ := (list (bsp_terms X)).

  Global Instance eqℒ : SemEquiv ℒ := (@eqLang _ equiv).
  Global Instance infℒ : SemSmaller ℒ := (@infLang _ equiv).
  
  Global Instance Box_list : Box ℒ := map box.

  Global Instance ℒ_BiSemiRing : BiSemiRing ℒ sequiv prod par join un zero
    := ListBiSemiRing_bisemiring.
  Global Instance ℒ_Idem : @Idempotent ℒ sequiv join
    := ListBiSemiRing_idempotent.
  
  Global Instance ℒ_box_proper_inf : Proper (ssmaller ==> ssmaller) box.
  Proof.
    unfold box,Box_list;intros l m I x Ix;apply in_map_iff in Ix as (y&<-&Iy).
    apply I in Iy as (z&Iz&Ez).
    setoid_rewrite <- Ez.
    exists (▢ z);split;[apply in_map_iff;exists z;tauto|reflexivity].
  Qed.
  Global Instance ℒ_box_proper_eq : Proper (sequiv ==> sequiv) box.
  Proof. intros l m (E1&E2);split;apply ℒ_box_proper_inf;assumption. Qed.
    
  Fixpoint termLang s : list (bsp_terms X) :=
    match s with
    | bbsr_par s1 s2 => termLang s1 ∥ termLang s2
    | bbsr_seq s1 s2 => termLang s1 ⋅ termLang s2
    | bbsr_plus s1 s2 => termLang s1 ∪ termLang s2
    | bbsr_box s => ▢ (termLang s)
    | bbsr_unit => 𝟭
    | bbsr_zero => 𝟬
    | bbsr_var x => [bsp_var x]
    end.

  Lemma termLang_proper_Ax (Ax : relation bbsr_terms) :
    (Proper (Ax ==> sequiv) termLang) -> (Proper ((bbsr_eq Ax) ==> sequiv) termLang).
  Proof.
    intros hAx e f E;induction E.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - unfold interpret;simpl;rewrite IHE1,IHE2;reflexivity.
    - unfold interpret;simpl;rewrite IHE1,IHE2;reflexivity.
    - unfold interpret;simpl;rewrite IHE1,IHE2;reflexivity.
    - unfold interpret;simpl;rewrite IHE;reflexivity.
    - apply hAx,H.
  Qed.

  Lemma termLang_proper_bisemiring : Proper (bisemiring ==> sequiv) termLang.
  Proof.
    intros e f [];simpl.
    - apply mon_assoc.
    - apply mon_assoc.
    - apply mon_assoc.
    - apply bimon_comm.
    - apply bisemiring_comm.
    - apply ℒ_Idem.
    - apply left_unit.
    - apply right_unit.
    - apply left_unit.
    - apply left_unit.
    - apply left_absorbing.
    - apply right_absorbing.
    - apply left_absorbing.
    - apply bisemiring_left_distr.
    - apply bisemiring_right_distr.
    - apply bisemiring_par_distr.
  Qed.
  
  Lemma termLang_proper_box_alg : Proper (box_alg ==> sequiv) termLang.
  Proof.
    intros e f [];simpl.
    - unfold box,Box_list;rewrite map_map.
      split;intros x Ix.
      + apply in_map_iff in Ix as (y&<-&Iy).
        exists (▢ y);split;auto.
        apply in_map_iff;exists y;tauto.
      + apply in_map_iff in Ix as (y&<-&Iy).
        exists (▢(▢y));split;auto.
        apply in_map_iff;exists y;split;auto.
    - unfold box,Box_list.
      split;intros x Ix.
      + apply in_map_iff in Ix as (y&<-&[<-|F]);[|exfalso;apply F].
        exists 𝟭;split;simpl;auto.
      + destruct Ix as [<-|F];[|exfalso;apply F].
        exists (▢ 𝟭);split;auto.
        apply in_map_iff ;exists 𝟭;split;simpl;auto.
    - unfold box,Box_list;simpl;reflexivity.
    - unfold box,Box_list,join,join_list.
      rewrite map_app;reflexivity.
  Qed.
  
  Fixpoint from_term (t : bsp_terms X) :=
    match t with
    | bsp_var x => bbsr_var x
    | bsp_unit => 𝟭
    | bsp_seq s1 s2 => from_term s1 ⋅ from_term s2
    | bsp_par s1 s2 => from_term s1 ∥ from_term s2
    | bsp_box s => ▢ (from_term s)
    end.

  Lemma from_term_termLang t : termLang (from_term t) ≃ [t].
  Proof.
    induction t;simpl.
    - rewrite IHt1,IHt2;clear;split; intros x.
      + intros I;unfold prod,prod_list in I;apply lift_prod_spec in I as (a&b&Ia&Ib&->).
        destruct Ia as [<-|Fa],Ib as [<-|Fb];try (exfalso;apply Fa||apply Fb).
        exists (t1⋅t2);split;[left|];reflexivity.
      + intros [<-|F];[|exfalso;apply F].
        exists (t1⋅t2);split;[|reflexivity].
        apply lift_prod_spec;exists t1,t2;repeat split;left;reflexivity.
    - rewrite IHt1,IHt2;clear;split; intros x.
      + intros I;unfold par,par_list in I;apply lift_prod_spec in I as (a&b&Ia&Ib&->).
        destruct Ia as [<-|Fa],Ib as [<-|Fb];try (exfalso;apply Fa||apply Fb).
        exists (t1∥t2);split;[left|];reflexivity.
      + intros [<-|F];[|exfalso;apply F].
        exists (t1∥t2);split;[|reflexivity].
        apply lift_prod_spec;exists t1,t2;repeat split;left;reflexivity.
    - reflexivity.
    - rewrite IHt;simpl.
      unfold box,Box_list;simpl;reflexivity.
    - reflexivity.
  Qed.
  Lemma termLang_from_term e :
    BSR ⊢ Σ (map from_term (termLang e)) ⩵ e.
  Proof.
    induction e;simpl.
    - rewrite <- IHe1 , <-IHe2 at 2.
      clear;replace bbsr_seq with prod by reflexivity.
      rewrite Σ_prod;apply Σ_proper;simpl.
      unfold interpret;generalize (termLang e2);generalize (termLang e1);intros l m.
      induction l as [|x l IHl];[reflexivity|].
      simpl;unfold prod,prod_list in *;simpl.
      rewrite map_app,map_map,IHl.
      apply mon_congr;[|reflexivity].
      rewrite map_map;simpl;reflexivity.
    - rewrite <- IHe1 , <-IHe2 at 2.
      clear;replace bbsr_par with par by reflexivity.
      rewrite Σ_par;apply Σ_proper;simpl.
      unfold interpret;generalize (termLang e2);generalize (termLang e1);intros l m.
      induction l as [|x l IHl];[reflexivity|].
      simpl;unfold par,par_list in *;simpl.
      rewrite map_app,map_map,IHl.
      apply mon_congr;[|reflexivity].
      rewrite map_map;simpl;reflexivity.
    - unfold join,join_list.
      rewrite map_app;rewrite <-IHe1,<-IHe2 at 2.
      symmetry;eapply Σ_app.
    - apply right_unit. 
    - unfold box,Box_list;rewrite map_map;simpl.
      rewrite <- IHe at 2;clear IHe.
      induction (termLang e) as [|b l Ihl];rsimpl.
      + symmetry;apply bbsr_ax;right;auto.
      + rsimpl. 
        etransitivity;[|symmetry;apply bbsr_ax;right;apply bbsr_eq_box_plus].
        rewrite <- Ihl;reflexivity.
    - apply right_unit.
    - reflexivity.
  Qed.

  Global Instance from_term_proper : Proper (equiv ==> bbsr_eq BSR) from_term.
  Proof.
    intros s t E;induction E;simpl;auto.
    - eauto.
    - apply mon_assoc.
    - apply mon_assoc.
    - apply bimon_comm.
    - apply left_unit.
    - apply right_unit.
    - apply left_unit.
    - weak_right;auto.
    - weak_right;auto.
  Qed.

  Lemma bcsr_exchange_law :
    forall a b c d : (@bbsr_terms X), BCSR ⊢ (a ∥ b) ⋅ (c ∥ d) ≦ a ⋅ c ∥ b ⋅ d.
  Proof. intros;unfold leqA;symmetry;weak_right;apply bbsr_ax;auto. Qed.
  
  Lemma bcsr_box_inf :
    forall a : @bbsr_terms X, BCSR ⊢ ▢ a ≦ a.
  Proof. intros a;unfold leqA;symmetry;weak_right;apply bbsr_ax;auto. Qed.
  
  Global Instance from_term_proper_inf : Proper (subsume ==> leqA (bbsr_eq BCSR)) from_term.
  Proof.
    intros s t E;induction E;simpl;auto.
    - apply from_term_proper in H;rewrite H;reflexivity.
    - rewrite IHE,IHE0;reflexivity.
    - rewrite IHE,IHE0;reflexivity.
    - rewrite IHE,IHE0;reflexivity.
    - rewrite IHE;reflexivity.
    - apply bcsr_exchange_law.
    - apply bcsr_box_inf.
  Qed.

  Corollary termLang_iso e f : BSR ⊢ e ⩵ f <-> (termLang e) ≃ (termLang f).
  Proof.
    split.
    - apply termLang_proper_Ax.
      intros s t [h|h];revert h.
      + apply termLang_proper_bisemiring.
      + apply termLang_proper_box_alg.
    - intros E.
      etransitivity;[symmetry;apply termLang_from_term|].
      etransitivity;[|apply termLang_from_term].
      apply antisymmetry.
      + apply Σ_bounded.
        intros a Ia.
        apply in_map_iff in Ia as (s&<-&Is).
        apply E in Is as (b&Ib&<-). 
        apply Σ_bigger,in_map_iff;exists b;tauto.
      + apply Σ_bounded.
        intros a Ia.
        apply in_map_iff in Ia as (s&<-&Is).
        apply E in Is as (b&Ib&<-). 
        apply Σ_bigger,in_map_iff;exists b;tauto.
  Qed.
  Lemma from_term_pomsets s :
    lift [⟦s⟧] ≃ ⟦from_term s⟧.
  Proof.
    induction s;rsimpl.
    - rewrite <- IHs1,<-IHs2;clear IHs1 IHs2.
      intro;unfold lift,mem;simpl.
      split;[intros (y&[<-|F]&E)|intros (u1&u2&E&(v1&[<-|F1]&E1)&(v2&[<-|F2]&E2))];
        try (exfalso;apply F||apply F1||apply F2).
      + exists ⟦s1⟧,⟦s2⟧;repeat split.
        * symmetry;assumption.
        * eexists;split;[left;reflexivity|reflexivity].
        * eexists;split;[left;reflexivity|reflexivity].
      + exists (⟦ s1 ⟧ ⋅ ⟦ s2 ⟧).
        rewrite E,<- E1,<-E2.
        split;[tauto|reflexivity].
    - rewrite <- IHs1,<-IHs2;clear IHs1 IHs2.
      intro;unfold lift,mem;simpl.
      split;[intros (y&[<-|F]&E)|intros (u1&u2&E&(v1&[<-|F1]&E1)&(v2&[<-|F2]&E2))];
        try (exfalso;apply F||apply F1||apply F2).
      + exists ⟦s1⟧,⟦s2⟧;repeat split.
        * symmetry;assumption.
        * eexists;split;[left;reflexivity|reflexivity].
        * eexists;split;[left;reflexivity|reflexivity].
      + exists (⟦ s1 ⟧ ∥ ⟦ s2 ⟧).
        rewrite E,<- E1,<-E2.
        split;[tauto|reflexivity].
    - intro;simpl;unfold lift,mem;simpl.
      unfold interpret;simpl;reflexivity.
    - rewrite <- IHs.
      intro;simpl;unfold lift,mem;simpl.
      split.
      + intros (y&[<-|F]&E);[|exfalso;apply F].
        exists ⟦s⟧;split;[|symmetry;assumption].
        exists ⟦s⟧;split;[tauto|reflexivity].
      + intros (q&(p&[<-|F]&E1)&E2);[|exfalso;apply F].
        exists (▢ ⟦ s ⟧);split;[tauto|].
        rewrite E1,<-E2;reflexivity.
    - intro;simpl;unfold lift,mem;simpl.
      split.
      + intros (?&[<-|F]&<-);[reflexivity|tauto].
      + intros E;exists 𝟭;symmetry in E;tauto.
  Qed.
              

  Lemma termLang_pomsets s :
    ⟦s⟧ ≃ lift (map interpret (termLang s)).
  Proof.
    rewrite <- (termLang_from_term s) at 1.
    induction (termLang s);rsimpl.
    - intro;simpl;split;[tauto|].
      intros (?&F&_);apply F.
    - rewrite IHl;clear IHl.
      rewrite <- from_term_pomsets.
      setoid_rewrite <-join_list_eq.
      reflexivity.
  Qed.
End s.


Require Import pomset_isomorphism.
Section bsr.
  Context {X : Set} {decX : decidable_set X}.
  
  Theorem completeness_bbsr_terms (s t : @bbsr_terms X) :
    BSR ⊢ s ⩵ t <-> ⟦s⟧ ≃ ⟦t⟧.
  Proof.
    split;[apply soundness_bbsr_terms|].
    intros Is.
    rewrite <- (termLang_from_term s),<- (termLang_from_term t).
    rewrite (termLang_pomsets s),(termLang_pomsets t) in Is.
    apply antisymmetry.
    - apply Σ_bounded.
      intros f If.
      apply in_map_iff in If as (u&<-&Iu).
      assert (Iu' : ⟦u⟧ ∊ (lift (map interpret (termLang s))))
        by (exists ⟦u⟧;split;[apply in_map_iff;exists u;tauto|reflexivity]).
      apply Is in Iu' as (p&Iv&Ev);apply in_map_iff in Iv as (v&<-&Iv).
      apply completeness_bsp_terms_iso in Ev.
      apply from_term_proper in Ev as <-.
      apply Σ_bigger,in_map_iff;exists v;tauto.
    - apply Σ_bounded.
      intros f If.
      apply in_map_iff in If as (u&<-&Iu).
      assert (Iu' : ⟦u⟧ ∊ (lift (map interpret (termLang t))))
        by (exists ⟦u⟧;split;[apply in_map_iff;exists u;tauto|reflexivity]).
      apply Is in Iu' as (p&Iv&Ev);apply in_map_iff in Iv as (v&<-&Iv).
      apply completeness_bsp_terms_iso in Ev.
      apply from_term_proper in Ev as <-.
      apply Σ_bigger,in_map_iff;exists v;tauto.
  Qed.
End bsr.

Require Import pomset_homomorphism.
Section bcsr.
  Context {X : Set} {decX : decidable_set X}.
  
  Theorem completeness_bcsr_terms (s t : @bbsr_terms X) :
   BCSR ⊢ s ⩵ t <-> ⟦s⟧↓ ≃ ⟦t⟧↓.
  Proof.
    split;[apply soundness_bcsr_terms|].
    intros Is.
    assert (L1 : ⟦s⟧↓ ≲ ⟦t⟧↓) by (rewrite Is;reflexivity).
    assert (L2 : ⟦t⟧↓ ≲ ⟦s⟧↓) by (rewrite Is;reflexivity).
    rewrite closure_incl in L1,L2;clear Is.
    rewrite <-(termLang_from_term s).
    rewrite <-(termLang_from_term t).
    rewrite (termLang_pomsets s),(termLang_pomsets t) in L1,L2.
    apply antisymmetry.
    - apply Σ_bounded.
      intros f If.
      apply in_map_iff in If as (u&<-&Iu).
      assert (Iu' : ⟦u⟧ ∊ (algebra.lift (map interpret (termLang s))))
        by (exists ⟦u⟧;split;[apply in_map_iff;exists u;tauto|reflexivity]).
      apply L1 in Iu' as (q&(p&Iv&Ev)&L).
      apply in_map_iff in Iv as (v&<-&Iv).
      rewrite <- Ev in L;clear q Ev.
      apply completeness_subsumption in L.
      apply from_term_proper_inf in L as ->.
      apply Σ_bigger,in_map_iff;exists v;tauto.
    - apply Σ_bounded.
      intros f If.
      apply in_map_iff in If as (u&<-&Iu).
      assert (Iu' : ⟦u⟧ ∊ (algebra.lift (map interpret (termLang t))))
        by (exists ⟦u⟧;split;[apply in_map_iff;exists u;tauto|reflexivity]).
      apply L2 in Iu' as (q&(p&Iv&Ev)&L).
      apply in_map_iff in Iv as (v&<-&Iv).
      rewrite <- Ev in L;clear q Ev.
      apply completeness_subsumption in L.
      apply from_term_proper_inf in L as ->.
      apply Σ_bigger,in_map_iff;exists v;tauto.
  Qed.
End bcsr.
    