Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools algebra Bool relations finite_expr pomsets.

Section s.
  Context {X : Set}.  

  Definition PomLang := SetBiKA (Pomset X) sequiv.

  Global Instance BoxPomLang : Box PomLang :=
    fun L => exist _ (fun p => exists q, q ∊ L /\ p ≃ ▢ q) _.
  Proof. intros p1 p2 E;setoid_rewrite E;reflexivity. Defined.
                           
  Global Instance BoxPomLang_smaller : Proper (ssmaller ==> ssmaller) (@box _ BoxPomLang).
  Proof. intros L M E p;intros (q&Iq&->);exists q;(split;[apply E,Iq|reflexivity]). Qed.
  Global Instance BoxPomLang_equiv : Proper (sequiv ==> sequiv) (@box _ BoxPomLang).
  Proof. intros L M E p;split;intros (q&Iq&->);exists q;(split;[apply E,Iq|reflexivity]). Qed.
  
  
  Lemma PomLang_box_box (s : PomLang) : ▢ (▢ s) ≃ ▢ s.
  Proof.
    intro p;split.
    - intros (p'&(q&Iq&Eq)&Ep').
      exists q;split;[assumption|].
      rewrite Ep',Eq.
      apply Pomset_box_box.
    - intros (q&Iq&Eq).
      exists (▢ q);split.
      + exists q;split;[assumption|reflexivity].
      + rewrite Eq;symmetry;apply Pomset_box_box.
  Qed.
    
  Lemma PomLang_box_unit : ▢ 𝟭 ≃ (𝟭 : PomLang).
  Proof.
    intro p;split.
    - intros (q&I&E).
      simpl in *;rewrite E,I.
      apply Pomset_box_unit.
    - simpl;intros E.
      exists 𝟭;split;[reflexivity|].
      rewrite E;symmetry;apply Pomset_box_unit.
  Qed.
      
  Lemma PomLang_box_zero : ▢ 𝟬 ≃ (𝟬 : PomLang).
  Proof. intro;simpl;split;[intros (?&F&_)|];tauto. Qed.
  
  Lemma PomLang_box_plus (a b : PomLang) : ▢ (a∪b) ≃ (▢ a) ∪ (▢ b).
  Proof.
    intros p;split.
    - intros (q&[I|I]&E);[left|right];exists q;tauto.
    - intros [I|I];destruct I as (q&I&E);exists q;split;simpl;tauto.
  Qed.

  Definition in_closure (l : PomLang) p := exists q, q ∊ l /\ p ⊑ q.

  Lemma in_closure_proper l : Proper (sequiv ==> iff) (in_closure l).
  Proof. intros p p' E;unfold in_closure;setoid_rewrite E;reflexivity. Qed.
  
  Definition closure (l : PomLang) : PomLang :=
    exist _ (in_closure l) (in_closure_proper l).
  
  Notation " l ↓ " := (closure l) (at level 25).

  Global Instance closure_proper : Proper (ssmaller ==> ssmaller) closure.
  Proof.
    intros l m E p.
    rsimpl;unfold in_closure.
    intros (q&Iq&Eq);exists q;split;auto;apply E,Iq.
  Qed.
  Global Instance closure_proper_eq : Proper (sequiv ==> sequiv) closure.
  Proof. intros l m E;apply antisymmetry;apply closure_proper;rewrite E;reflexivity. Qed.
  
    
  Global Instance sem_fin : Semantics (@bbsr_terms X) PomLang :=
    fix I s :=
      match s with
      | bbsr_plus s1 s2 => I s1 ∪ I s2
      | bbsr_seq s1 s2 => I s1 ⋅ I s2
      | bbsr_par s1 s2 => I s1 ∥ I s2
      | bbsr_unit => 𝟭
      | bbsr_zero => 𝟬
      | bbsr_var x => lift [AtomicPomset x]
      | bbsr_box s => ▢ (I s)
      end.

  Remark interpret_bbsr_seq s1 s2 : ⟦s1⋅s2⟧ =  ⟦s1⟧⋅⟦s2⟧.
  Proof. reflexivity. Qed.
  Remark interpret_bbsr_plus s1 s2 : ⟦s1 ∪ s2⟧ =  ⟦s1⟧∪⟦s2⟧.
  Proof. reflexivity. Qed.
  Remark interpret_bbsr_par s1 s2 : ⟦s1∥s2⟧ =  ⟦s1⟧∥⟦s2⟧.
  Proof. reflexivity. Qed.
  Remark interpret_bbsr_box s : ⟦▢ s⟧ = ▢ ⟦s⟧.
  Proof. reflexivity. Qed.
  Remark interpret_bbsr_unit : ⟦𝟭⟧ = 𝟭.
  Proof. reflexivity. Qed.
  Remark interpret_bbsr_zero : ⟦𝟬⟧ = 𝟬.
  Proof. reflexivity. Qed.
  Hint Rewrite
       interpret_bbsr_seq interpret_bbsr_par interpret_bbsr_box interpret_bbsr_plus
    : simpl_typeclasses.

  Lemma soundness_ax_bbsr_terms Ax s t :
    Proper (Ax ==> sequiv) interpret -> Ax ⊢ s ⩵ t -> ⟦s⟧ ≃ ⟦t⟧.
  Proof.
    intros Pr E;induction E;rsimpl.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - rewrite IHE1,IHE2;reflexivity.
    - rewrite IHE1,IHE2;reflexivity.
    - rewrite IHE1,IHE2;reflexivity.
    - rewrite IHE;reflexivity.
    - rewrite H;reflexivity.
  Qed.
  
  Lemma soundness_bisemiring : Proper (bisemiring ==> sequiv) interpret.
  Proof.
    intros s t E;destruct E;rsimpl.
    - apply mon_assoc.
    - apply mon_assoc.
    - apply mon_assoc.
    - apply bimon_comm.
    - apply bisemiring_comm.
    - apply bika_idem.
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
      
  Lemma soundness_box_alg : Proper (box_alg ==> sequiv) interpret.
  Proof.
    intros s t E;destruct E;rsimpl.
    - apply PomLang_box_box.
    - apply PomLang_box_unit.
    - apply PomLang_box_zero.
    - apply PomLang_box_plus.
  Qed.
  
  Lemma soundness_bbsr_terms s t : BSR ⊢ s ⩵ t -> ⟦s⟧ ≃ ⟦t⟧.
  Proof.
    apply soundness_ax_bbsr_terms.
    intros e f [E|E].
    - apply soundness_bisemiring,E.
    - apply soundness_box_alg,E.
  Qed.

  Global Instance interpret_finexp_proper : Proper ((bbsr_eq BSR) ==> sequiv) interpret.
  Proof. intros x y; apply soundness_bbsr_terms. Qed.

  Lemma closure_incr l : l ≲ l↓.
  Proof. intros p I;exists p;split;[assumption|reflexivity]. Qed.
  Lemma closure_idem l : l ↓↓ ≃ l↓.
  Proof.
    apply antisymmetry;[|apply closure_incr].
    intros p (q&(q'&I&E')&E).
    exists q';split;[|etransitivity];eassumption.
  Qed.

  Proposition closure_incl l m : l ↓ ≲ m ↓ <-> l ≲ m ↓.
  Proof.
    split.
    - intros <-;apply closure_incr.
    - intros ->;rewrite closure_idem;reflexivity.
  Qed.
  
  Global Instance prodLang_proper :
    Proper (ssmaller ==> ssmaller ==> ssmaller) (fun l m : PomLang => l ⋅ m).
  Proof.
    intros l l' L m m' M p (p1&p2&E&I1&I2).
    exists p1,p2;split;[assumption|];split;[apply L,I1|apply M,I2].
  Qed.
  Global Instance parLang_proper :
    Proper (ssmaller ==> ssmaller ==> ssmaller) (fun l m : PomLang => l ∥ m).
  Proof.
    intros l l' L m m' M p (p1&p2&E&I1&I2).
    exists p1,p2;split;[assumption|];split;[apply L,I1|apply M,I2].
  Qed.
  Global Instance joinLang_proper :
    Proper (ssmaller ==> ssmaller ==> ssmaller) (fun l m : PomLang => l ∪ m).
  Proof.
    intros l l' L m m' M p [I|I].
    - left;apply L,I.
    - right;apply M,I.
  Qed.

  Lemma closure_prod l m : (l⋅m)↓ ≃ (l↓⋅m↓)↓.
  Proof.
    apply antisymmetry.
    - apply closure_proper.
      apply prodLang_proper;apply closure_incr.
    - intros p (p'&(p1&p2&E&(q1&I1&L1)&(q2&I2&L2))&L).
      rewrite E in L;clear p' E.
      exists (q1⋅q2);split.
      + exists q1,q2;split;[reflexivity|tauto].
      + rewrite L,L1,L2;reflexivity.
  Qed. 
  Lemma closure_par l m : (l∥m)↓ ≃ (l↓∥m↓)↓.
  Proof.
    apply antisymmetry.
    - apply closure_proper.
      apply parLang_proper;apply closure_incr.
    - intros p (p'&(p1&p2&E&(q1&I1&L1)&(q2&I2&L2))&L).
      rewrite E in L;clear p' E.
      exists (q1∥q2);split.
      + exists q1,q2;split;[reflexivity|tauto].
      + rewrite L,L1,L2;reflexivity.
  Qed.
  Lemma closure_box l : (▢ l)↓ ≃ (▢ (l↓))↓.
  Proof.
    apply antisymmetry.
    - apply closure_proper.
      apply BoxPomLang_smaller;apply closure_incr.
    - intros p (p'&(q&(q'&I&Lq)&E)&Lp).
      exists (▢ q');split.
      + exists q';split;[assumption|reflexivity].
      + rewrite Lp,E,Lq;reflexivity.
  Qed.
  Lemma closure_join l m : (l ∪ m)↓ ≃ l↓ ∪ m↓.
  Proof.
    apply antisymmetry.
    - intros p (q&[I|I]&L);[left|right];exists q;tauto.
    - intros p [I|I];destruct I as (q&I&E);exists q;split;simpl;auto.
  Qed.

  Corollary closure_smaller_equiv l m : l ↓ ≲ m ↓ <-> (l ∪ m) ↓ ≃ m ↓.
  Proof.
    etransitivity.
    - symmetry;apply SetBiKA_inf_is_impl.
    - unfold leqA.
      rewrite <- closure_join;split;intro;symmetry;assumption.
  Qed.
  
  Lemma soundness_bcsr_terms s t : BCSR ⊢ s ⩵ t -> ⟦s⟧↓ ≃ ⟦t⟧↓.
  Proof.
    intro E;induction E.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - rsimpl.
      rewrite closure_prod,IHE1,IHE2,<-closure_prod.
      reflexivity.
    - rsimpl.
      rewrite closure_par,IHE1,IHE2,<-closure_par.
      reflexivity.
    - rsimpl.
      repeat rewrite closure_join.
      rewrite IHE1,IHE2;reflexivity.
    - rsimpl.
      rewrite closure_box,IHE,<-closure_box.
      reflexivity.
    - destruct H as [[E|E]|E].
      + apply soundness_bisemiring in E as ->;reflexivity.
      + apply soundness_box_alg in E as ->;reflexivity.
      + destruct E.
        * rsimpl;apply closure_smaller_equiv.
          intros p (q&(r&s&E'&(A&B&E1&Ia&Ib)&(C&D&E2&Ic&Id))&E).
          rewrite E',E1,E2 in E.
          clear E' E1 E2 q r s.
          exists (A⋅C∥B⋅D);split.
          -- exists (A⋅C),(B⋅D);split;[reflexivity|].
             split.
             ++ exists A,C;split;[reflexivity|tauto].
             ++ exists B,D;split;[reflexivity|tauto].
          -- rewrite E;apply exchange_law. 
        * rsimpl;apply closure_smaller_equiv.
          intros p (p'&(q&I&Eq)&E);rewrite Eq in E;clear p' Eq.
          exists q;split;auto.
          rewrite E.
          apply Pomset_box_inf.
   Qed.

End s.
Notation " l ↓ " := (closure l) (at level 25).
      
Hint Rewrite
     @interpret_bbsr_plus @interpret_bbsr_seq @interpret_bbsr_par @interpret_bbsr_box
  : simpl_typeclasses.
