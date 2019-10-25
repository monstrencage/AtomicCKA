Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra Bool bindings.

Inductive bnd_terms : Set :=
| bnd_seq : bnd_terms -> bnd_terms -> bnd_terms
| bnd_par : bnd_terms -> bnd_terms -> bnd_terms
| bnd_b | bnd_o | bnd_c | bnd_0
| bnd_unit : bnd_terms.

Global Instance bnd_seq_prod : Product bnd_terms := bnd_seq.

Global Instance bnd_par_prod : ParProduct bnd_terms := bnd_par.

Global Instance bnd_unit_unit : Un bnd_terms := bnd_unit.

Global Instance bnd_Zero_zero : Zero bnd_terms := bnd_0.

Notation 𝗯 := bnd_b.
Notation 𝗼 := bnd_o.
Notation 𝗰 := bnd_c.

Inductive bnd_eq : Equiv bnd_terms :=
(** Equivalence relation. *)
| bnd_eq_refl s : s ≡ s
| bnd_eq_sym s t : s ≡ t -> t ≡ s
| bnd_eq_trans s t u : s ≡ t -> t ≡ u -> s ≡ u
(** Congruence. *)               
| bnd_eq_seq s t s' t' : s ≡ t -> s' ≡ t' -> s ⋅ s' ≡ t ⋅ t'
| bnd_eq_par s t s' t' : s ≡ t -> s' ≡ t' -> s ∥ s' ≡ t ∥ t'
(** Sequential monoid. *)
| bnd_eq_seq_left_unit s : 𝟭 ⋅ s ≡ s
| bnd_eq_seq_right_unit s : s ⋅ 𝟭 ≡ s         
| bnd_eq_seq_ass s t u : s ⋅ (t ⋅ u) ≡ (s ⋅ t) ⋅ u
(** Parallel monoid. *)
| bnd_eq_par_ass s t u : s ∥ (t ∥ u) ≡ (s ∥ t) ∥ u
| bnd_eq_par_comm s t : s ∥ t ≡ t ∥ s
| bnd_eq_par_unit s : 𝟭 ∥ s ≡ s
(** Zero. *)
| bnd_eq_zero_seq s : 𝟬 ⋅ s ≡ 𝟬 
| bnd_eq_seq_zero s : s ⋅ 𝟬 ≡ 𝟬
| bnd_eq_zero_par s : 𝟬 ∥ s ≡ 𝟬
(** Pseudo-unit. *)
| bnd_eq_b_o : 𝗯 ⋅ 𝗼 ≡ 𝗼
| bnd_eq_o_b : 𝗼 ⋅ 𝗯 ≡ 𝗼
| bnd_eq_b_c : 𝗯 ⋅ 𝗰 ≡ 𝗰
| bnd_eq_c_b : 𝗰 ⋅ 𝗯 ≡ 𝗰
| bnd_eq_b_b : 𝗯 ⋅ 𝗯 ≡ 𝗯
(** Balanced in parallel. *)
| bnd_eq_b_par_b : 𝗯 ∥ 𝗯 ≡ 𝗯
(** Open×Close=Balanced. *)
| bnd_eq_o_c : 𝗼 ⋅ 𝗰 ≡ 𝗯
(** Cancel rubbish parallel products. *)
| bnd_eq_b_par_c s t : (𝗯⋅s) ∥ (𝗰 ⋅ t) ≡ 𝟬
| bnd_eq_b_par_o s t : (𝗯⋅s) ∥ (t ⋅ 𝗼) ≡ 𝟬.
Hint Constructors bnd_eq.
Global Instance bnd_eq_Equiv : Equiv bnd_terms := bnd_eq.

Global Instance bnd_eq_Equivalence : Equivalence equiv.
Proof. split;intro;intros;eauto. Qed.

Global Instance bnd_terms_bimonoid : BiMonoid bnd_terms equiv prod par un.
Proof. repeat split;repeat intro;eauto. Qed.

Global Instance bnd_zero_seq : @Absorbing bnd_terms equiv prod zero.
Proof. split;intro;auto. Qed.
Global Instance bnd_zero_par : @Absorbing bnd_terms equiv par zero.
Proof. split;intro;[|rewrite bnd_eq_par_comm];auto. Qed.


Global Instance toBnd : Semantics bnd_terms binding :=
  fix I s :=
    match s with
    | bnd_seq s1 s2 => I s1 ⋅ I s2
    | bnd_par s1 s2 => I s1 ∥ I s2
    | bnd_b => 𝒷
    | bnd_o => ℴ
    | bnd_c => 𝒸
    | bnd_0 => ↯
    | bnd_unit => ℯ
    end.

Definition fromBnd β :=
  match β with
  | ℯ => 𝟭
  | ↯ => 𝟬
  | Bnd n m => (𝗰 ^ n) ⋅ 𝗯 ⋅ (𝗼 ^ m)
  end.

Lemma toBnd_fromBnd β : ⟦fromBnd β⟧ = β.
Proof.
  destruct β as [| |n m];simpl;try reflexivity.
  unfold interpret;simpl;induction n;simpl.
  - rewrite left_unit.
    induction m;simpl.
    + reflexivity.
    + transitivity (ℴ⋅(Bnd 0 m)).
      * rewrite <- IHm.
        repeat rewrite (mon_assoc _);reflexivity.
      * unfold prod,SeqBind;f_equal;clear.
        lia.
  - repeat rewrite <- (mon_assoc _).
    rewrite (mon_assoc _ 𝒷),IHn.
    unfold prod,SeqBind;f_equal;clear;lia.
Qed.

Lemma bnd_eq_b_pow_o n : 𝗯 ⋅ 𝗼 ^ n ≡ 𝗼 ^ n ⋅ 𝗯.
Proof.
  destruct n.
  - simpl;rewrite left_unit,right_unit;reflexivity.
  - transitivity (𝗼 ^ (S n)).
    + simpl;rewrite (mon_assoc _),bnd_eq_b_o;reflexivity.
    + rewrite Power_last,<- (mon_assoc _),bnd_eq_o_b;reflexivity.
Qed.
Lemma bnd_eq_b_pow_c n : 𝗯 ⋅ 𝗰 ^ n ≡ 𝗰 ^ n ⋅ 𝗯.
Proof.
  destruct n.
  - simpl;rewrite left_unit,right_unit;reflexivity.
  - transitivity (𝗰 ^ (S n)).
    + simpl;rewrite (mon_assoc _),bnd_eq_b_c;reflexivity.
    + rewrite Power_last,<- (mon_assoc _),bnd_eq_c_b;reflexivity.
Qed.
Lemma bnd_eq_ok_ck k : 0 < k -> 𝗼 ^ k ⋅ 𝗰 ^ k ≡ 𝗯.
Proof.
  induction k;[lia|destruct k].
  - intros _;simpl;repeat rewrite right_unit.
    apply bnd_eq_o_c.
  - intros _.
    rewrite (Power_last 𝗰),(mon_assoc _).
    simpl.
    rewrite <-(mon_assoc 𝗼).
    rewrite IHk by lia.
    eauto.
Qed.
  
Lemma fromBnd_prod α β : fromBnd (α⋅β) ≡ fromBnd α ⋅ fromBnd β.
Proof.
  destruct α as [| |n m],β as [| |k l];simpl.
  - repeat rewrite left_unit;reflexivity.
  - auto.
  - rewrite left_unit;reflexivity.
  - auto.
  - auto.
  - auto.
  - rewrite right_unit;reflexivity.
  - auto.
  - replace (l + (m-k)) with ((m-k)+l) by lia.
    rewrite (Power_add _ (m-k) l).
    repeat rewrite (mon_assoc _).
    apply bnd_eq_seq;[clear l|reflexivity].
    repeat rewrite <- bnd_eq_b_pow_c.
    repeat rewrite <- (mon_assoc _ _).
    repeat rewrite <- bnd_eq_b_pow_c.
    rewrite (mon_assoc _ 𝗯).
    rewrite <- bnd_eq_b_pow_o.
    rewrite (mon_assoc _ (𝗯 ⋅_)).
    rewrite (mon_assoc _ 𝗯).
    rewrite <- bnd_eq_b_pow_c.
    repeat rewrite (mon_assoc _).
    rewrite bnd_eq_b_b.
    induction n.
    + simpl;rewrite right_unit.
      destruct (Compare_dec.le_ge_dec k m) as [L|L].
      * replace (k - m) with 0 by lia.
        replace m with ((m-k)+k) at 2 by lia.
        generalize (m-k);clear m L.
        intros n.
        simpl;rewrite right_unit.
        rewrite Power_add,(mon_assoc _).
        repeat rewrite <- (mon_assoc _).
        destruct k.
        -- simpl;repeat rewrite right_unit;reflexivity.
        -- rewrite bnd_eq_ok_ck by lia.
           rewrite <- bnd_eq_b_pow_o.
           rewrite (mon_assoc _),bnd_eq_b_b.
           reflexivity.
      * replace (m - k) with 0 by lia.
        replace k with (m+(k-m)) at 2 by lia.
        generalize (k-m);clear k L.
        intros n.
        simpl;rewrite right_unit.
        rewrite Power_add,(mon_assoc _).
        apply bnd_eq_seq;[|reflexivity].
        repeat rewrite <- (mon_assoc _).
        destruct m.
        -- simpl;repeat rewrite right_unit;reflexivity.
        -- rewrite bnd_eq_ok_ck by lia.
           rewrite bnd_eq_b_b.
           reflexivity.
    + simpl.
      repeat rewrite (mon_assoc _).
      rewrite bnd_eq_b_c at 1.
      rewrite <- bnd_eq_c_b at 1.
      repeat rewrite <- (mon_assoc _) in *.
      rewrite IHn.
      repeat rewrite (mon_assoc _).
      rewrite bnd_eq_b_c,bnd_eq_c_b.
      reflexivity.
Qed.
Lemma fromBnd_par α β : fromBnd (α∥β) ≡ fromBnd α ∥ fromBnd β.
Proof.
  destruct α as [| |n m],β as [| |k l];simpl;auto.
  - repeat rewrite right_unit;reflexivity.
  - repeat rewrite right_absorbing;reflexivity.
  - destruct n.
    + destruct m.
      * destruct k.
        -- destruct l.
           ++ simpl.
              repeat rewrite left_unit||rewrite right_unit.
              auto.
           ++ simpl.
              repeat rewrite left_unit||rewrite right_unit.
              rewrite (mon_assoc _),bnd_eq_b_o.
              rewrite <- bnd_eq_b_b;symmetry.
              replace (𝗼⋅𝗼^l) with (𝗼^(S l)) by reflexivity.
              rewrite Power_last;auto.
        -- simpl.
           repeat rewrite left_unit||rewrite right_unit.
           repeat rewrite <- (mon_assoc _).
           rewrite <- bnd_eq_b_b;symmetry;auto.
      * simpl.                         
        repeat rewrite left_unit||rewrite right_unit.
        replace (𝗼⋅𝗼^m) with (𝗼^(S m)) by reflexivity.
        rewrite Power_last;auto.
        rewrite <- bnd_eq_b_pow_c,<-(mon_assoc _).
        symmetry.
        rewrite (mon_assoc _).
        rewrite bnd_eq_par_comm;auto.
    + simpl;rewrite <- bnd_eq_b_pow_c.
      repeat rewrite <- (mon_assoc _).
      rewrite bnd_eq_par_comm;auto.
Qed.

Lemma fromBnd_toBnd β : fromBnd ⟦ β ⟧ ≡ β.
Proof.
  unfold interpret;induction β;simpl.
  - rewrite fromBnd_prod,IHβ1,IHβ2;reflexivity.
  - rewrite fromBnd_par,IHβ1,IHβ2;reflexivity.
  - repeat rewrite left_unit||rewrite right_unit;reflexivity.
  - repeat rewrite left_unit||rewrite right_unit;auto. 
  - repeat rewrite left_unit||rewrite right_unit;auto.
  - reflexivity.
  - reflexivity.
Qed.

Instance toBnd_proper : Proper (equiv ==> Logic.eq) toBnd.
Proof.
  intros e f E;induction E;simpl;auto;try congruence.
  - apply left_unit.
  - apply right_unit.
  - apply mon_assoc.
  - apply mon_assoc.
  - apply bimon_comm.
  - apply left_unit.
  - apply right_absorbing.
  - rewrite (bimon_comm _).
    destruct (toBnd t) as [| |k l].
    + destruct (toBnd s) as [| |n m];reflexivity. 
    + reflexivity.
    + destruct (toBnd s) as [| |n m];reflexivity. 
  - rewrite (bimon_comm _).
    destruct (toBnd t) as [| |k l].
    + destruct (toBnd s) as [| |n m];reflexivity. 
    + reflexivity.
    + unfold prod at 1,SeqBind;simpl_nat;simpl.
      destruct (toBnd s) as [| |n m];destruct k;reflexivity.
Qed.

Theorem binding_completeness s t : s ≡ t <-> ⟦s⟧ = ⟦t⟧.
Proof.
  split;[apply toBnd_proper|].
  rewrite <- (fromBnd_toBnd s) at 2.
  rewrite <- (fromBnd_toBnd t) at 2.
  intros ->;reflexivity.
Qed.

Remark injective_encoding s t : s = t <-> fromBnd s ≡ fromBnd t.
Proof.
  split;[intros ->;reflexivity|].
  rewrite <- (toBnd_fromBnd s) at 2.
  rewrite <- (toBnd_fromBnd t) at 2.
  intros ->;reflexivity.
Qed.
