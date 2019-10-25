Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra Bool.

Inductive binding : Set :=
| Emp | Err 
| Bnd : nat-> nat -> binding.

Notation 𝒷 := (Bnd 0 0).
Notation ℴ := (Bnd 0 1).
Notation 𝒸 := (Bnd 1 0).
Notation ℯ := Emp.
Notation " ↯ " := Err.

Global Instance dec_binding : decidable_set binding.
Proof.
  set (eqX := fun a b => match a,b with Emp,Emp
                                | Err,Err => true
                                | Bnd n m,Bnd n' m' => (n=?=n') && (m=?=m')
                                | _,_ => false end).
  apply (@Build_decidable_set _ eqX).
  intros x y;apply iff_reflect.
  destruct x as [| |n m],y as [| |n' m'];simpl;split;discriminate||auto;
    rewrite andb_true_iff;repeat rewrite PeanoNat.Nat.eqb_eq.
  - intros E;inversion E;subst;auto.
  - intros (->&->);reflexivity.
Qed.

Global Instance size_binding : Size binding :=
  fun b =>
    match b with
    | Emp | Err => 0
    | Bnd n m => n+m
    end.

Instance Emp_Un : Un binding := ℯ.

Global Instance SeqBind : Product binding :=
  fun u v =>
    match u,v with
    | Err,_ | _,Err => Err
    | Emp,u | u,Emp => u
    | Bnd n1 m1,Bnd n2 m2 => Bnd (n1+(n2-m1)) (m2+(m1-n2))
    end.

Global Instance ParBind : ParProduct binding :=
  fun u v =>
    match u,v with
    | Err,_ | _,Err => Err
    | Emp,u | u,Emp => u
    | Bnd 0 0,Bnd 0 0 => Bnd 0 0
    | _,_ => Err 
    end.

Global Instance Binding_zero : Zero binding := ↯.

Remark bindingUn : ℯ = 𝟭.
Proof. reflexivity. Qed.
Remark bindingZero : ↯ = 𝟬.
Proof. reflexivity. Qed.
Remark sizeEmp : ⎢𝟭⎥ = 0.
Proof. reflexivity. Qed.
Remark sizeErr : ⎢𝟬⎥ = 0.
Proof. reflexivity. Qed.
Remark sizeBnd n m : ⎢Bnd n m⎥ = n+m.
Proof. reflexivity. Qed.

Hint Rewrite bindingUn bindingZero sizeErr sizeEmp sizeBnd : simpl_typeclasses.

Lemma bind_eq_seq_ass u v w : (u⋅v)⋅w = u⋅(v⋅w).
Proof. destruct u,v,w;simpl;unfold prod;simpl;reflexivity||(f_equal;lia). Qed.
  
Lemma bind_eq_par_ass u v w : (u∥v)∥w = u∥(v∥w).
Proof.
  destruct u as [| |n1 m1],v as [| |n2 m2],w as [| |n3 m3];simpl;unfold par;simpl;
    try reflexivity
    ||(try destruct n1;auto;try destruct n2;auto;try destruct n3;auto;
      try destruct m1;auto;try destruct m2;auto;try destruct m3;auto).
Qed.

Lemma bind_eq_par_comm u v : u ∥ v = v ∥ u.
Proof. destruct u as [| |[] []],v as [| |[][]];simpl;unfold par;simpl;reflexivity. Qed.

Lemma bind_eq_e_seq_u u : ℯ ⋅ u = u.
Proof. destruct u;reflexivity. Qed.

Lemma bind_eq_e_par_u u : ℯ ∥ u = u.
Proof. destruct u;reflexivity. Qed.

Lemma bind_eq_u_seq_e u : u ⋅ ℯ = u.
Proof. destruct u;reflexivity. Qed.

Lemma bind_eq_b_seq_b : 𝒷 ⋅ 𝒷  = 𝒷.
Proof. reflexivity. Qed.
Lemma bind_eq_b_par_b : 𝒷 ∥ 𝒷  = 𝒷.
Proof. reflexivity. Qed.
Lemma bind_eq_o_seq_c : ℴ ⋅ 𝒸  = 𝒷.
Proof. reflexivity. Qed.
Lemma bind_eq_o_seq_b : ℴ ⋅ 𝒷  = ℴ.
Proof. reflexivity. Qed.
Lemma bind_eq_b_seq_c : 𝒷 ⋅ 𝒸  = 𝒸.
Proof. reflexivity. Qed.
Lemma bind_eq_c_seq_b : 𝒸 ⋅ 𝒷  = 𝒸.
Proof. reflexivity. Qed.
Lemma bind_eq_b_seq_o : 𝒷 ⋅ℴ  = ℴ.
Proof. reflexivity. Qed.

Global Instance BiMonoid_binding : (@BiMonoid _ Logic.eq prod par ℯ).
Proof.
  split.
  - split.
    + intro;intros;congruence.
    + intro;intros;symmetry;apply bind_eq_seq_ass.
    + split.
      * apply bind_eq_e_seq_u.
      * apply bind_eq_u_seq_e.
  - split.
    + intro;intros;congruence.
    + intro;intros;symmetry;apply bind_eq_par_ass.
    + split.
      * apply bind_eq_e_par_u.
      * intro;rewrite bind_eq_par_comm;apply bind_eq_e_par_u.
  - intros a b;apply bind_eq_par_comm.
Qed.

Global Instance Binding_zero_seq : @Absorbing binding Logic.eq prod zero.
Proof. split;intros [| |];reflexivity. Qed.
Global Instance Binding_zero_par : @Absorbing binding Logic.eq par zero.
Proof. split;intros [| |[] []];reflexivity. Qed.

Definition 𝔹 := SetBiKA binding Logic.eq.

Lemma all_sets_are_nice (P : binding -> Prop) : Proper (Logic.eq ==> iff) P.
Proof. intros u ? <-;reflexivity. Qed.

Definition make_𝔹 (P : binding -> Prop) : 𝔹 := exist _ P (all_sets_are_nice P).
Notation " ⟨ P ⟩ " := (make_𝔹 P).
Notation " ⟨| L |⟩ " := ⟨fun b => b ∈ L⟩.

Global Instance BindingUn : Un 𝔹 := SetBiKAUn.
Global Instance BindingZero : Zero 𝔹 := SetBiKAZero.
Global Instance BindingJoin : Join 𝔹 := SetBiKAJoin.
Global Instance BindingProd : Product 𝔹 := SetBiKAProd.
Global Instance BindingPar : ParProduct 𝔹 := SetBiKAPar.
Global Instance BindingStar : Star 𝔹 := SetBiKAStar.
Global Instance Binding_biKA : BiKleeneAlgebra 𝔹 sequiv:= SetBiKA_biKA.

Definition balanced b := match b with ℯ | 𝒷 => True | _ => False end.
Definition finite (B : 𝔹) := exists L, ~ ↯ ∈ L /\ B ≲ ⟨|L|⟩.
Definition sym b := match b with ℯ => True | Bnd n m => n=m | _ => False end.

Lemma finite_1 : finite 𝟭.
Proof.
  exists [ℯ];split;simpl;auto.
  - intros [E|E];inversion E.
  - intro;simpl;firstorder.
Qed.

Lemma finite_0 : finite 𝟬.
Proof.
  exists [];split;simpl;auto.
  intro;simpl;firstorder.
Qed.
Lemma finite_seq : forall B1 B2, finite B1 -> finite B2 -> finite (B1⋅B2).
Proof.
  intros B1 B2 (L1&N1&E1) (L2&N2&E2);exists (flat_map (fun b => map (prod b) L2) L1);split.
  - intros I;apply in_flat_map in I as (x&Ix&I).
    apply in_map_iff in I as (y&E&Iy).
    destruct x,y;unfold prod,SeqBind in E;simpl in *;try discriminate||tauto.
  - intros u;intros (u1&u2&->&I1&I2).
    simpl;apply in_flat_map;exists u1;split;auto.
    + apply E1,I1.
    + apply in_map_iff;exists u2;split;auto.
      apply E2,I2.
Qed.
Lemma finite_join : forall B1 B2, finite B1 -> finite B2 -> finite (B1 ∪ B2).
Proof.
  intros B1 B2 (L1&N1&E1) (L2&N2&E2);exists (L1++L2);split.
  - intros I;apply in_app_iff in I as [I|I];tauto.
  - intros u [I1|I2].
    + simpl;apply in_app_iff;left;apply E1,I1. 
    + simpl;apply in_app_iff;right;apply E2,I2. 
Qed.

Definition bounded N := fun b => ⎢b⎥ <= N /\ b <> ↯.
Definition unbounded (B : 𝔹) := ↯ ∊ B \/ forall N, exists b, b ∊ B /\ N < ⎢b⎥.

Lemma size_binding_finite N : finite ⟨bounded N⟩.
Proof.
  induction N.
  - exists [ℯ;Bnd 0 0];split.
    + simpl;firstorder discriminate.
    + intros [| |[] []] (Sb&N);rsimpl in *;lia||tauto.
  - destruct IHN as (L&E&I).
    exists (flat_map (fun b => match b with
                       | Bnd n m => [Bnd (S n)m;Bnd n (S m);Bnd n m]
                       | c => [c] end) L);split.
    + intros F;apply in_flat_map in F as ([| |k l]&I'&F);simpl in *;firstorder discriminate.
    + intros [| |n m] (Sb&Eb).
      * apply in_flat_map;exists ℯ;split;simpl;auto.
        apply I;split;rsimpl;lia||auto.
      * tauto.
      * apply PeanoNat.Nat.le_succ_r in Sb as [Sb|Sb].
        -- apply in_flat_map;exists (Bnd n m);split;simpl;auto.
           apply I;split;simpl;lia||auto.
        -- simpl in Sb.
           destruct n;simpl in *.
           ++ subst;apply in_flat_map;exists (Bnd 0 N);split;simpl;auto.
              apply I;split;auto.
              discriminate.
           ++ apply in_flat_map;exists (Bnd n m);split;simpl;auto.
              apply I;split;[|discriminate].
              rsimpl in *;lia.
Qed.

Lemma finite_iff_bounded B : finite B <-> exists N, B ≲ ⟨bounded N⟩.
Proof.
  split.
  - intros (L&E&I).
    set (N0 := fold_right max 0 (map size L)).
     exists N0;rewrite I;clear B I.
     induction L;simpl.
    + intro b;simpl;tauto.
    + intros b [<-|I].
      * split.
        -- unfold N0;rsimpl in *;lia.
        -- intros ->;apply E;now left.
      * split.
        -- apply IHL in I as (Sb&Nb).
           ++ etransitivity;[apply Sb|].
              unfold N0;simpl;lia.
           ++ intro I';apply E;now right.
        -- intros ->;apply E;now right.
  - intros (N&h__N).
    destruct(size_binding_finite N) as (L&EL&h__L).
    exists L;split;auto.
    rewrite h__N,h__L;reflexivity.
Qed.

Lemma unbounded_not_finite B : unbounded B -> ~ finite B.
Proof.
  intros [I|U] F.
  - destruct F as (L&E&I');apply E,I',I.
  - apply finite_iff_bounded in F as (N&IN).
    destruct (U N) as (b&Ib&Sb).
    apply IN in Ib as (Ib&_);lia.
Qed.
    
Lemma unbounded_seq_left :
  forall B1 B2 b, unbounded B1 -> b ∊ B2 -> unbounded (B1⋅B2).
Proof.
  intros B1 B2 b2 [I1|U] Ib2;[left;exists ↯,b2;split;auto|].
  destruct_eqX b2 ↯.
  - left.
    destruct (U 0) as (b&Ib&_);exists b,↯.
    rewrite right_absorbing;auto.
  - right.
    intros K.
    destruct (U (2*K+size b2)) as (b1&Ib1&Sb1).
    exists (b1⋅b2);split.
    + exists b1,b2;auto.
    + destruct b1 as [| |n1 m1],b2 as [| | n2 m2];unfold prod; rsimpl in *;tauto||lia.
Qed.

Lemma unbounded_seq_right :
  forall B1 B2 b, unbounded B2 -> b ∊ B1 -> unbounded (B1⋅B2).
Proof.
  intros B1 B2 b1 [I2|U] Ib1;[left;exists b1,↯;split;[destruct b1;reflexivity|auto]|].
  destruct_eqX b1 ↯.
  - left.
    destruct (U 0) as (b&Ib&_);exists ↯,b.
    rewrite left_absorbing;auto.
  - right.
    intros K.
    destruct (U (2*K+size_binding b1)) as (b2&Ib2&Sb2).
    exists (b1⋅b2);split.
    + exists b1,b2;auto.
    + destruct b1 as [| |n1 m1],b2 as [| | n2 m2];unfold prod;rsimpl in *;tauto||lia.
Qed.

Lemma sym_e : ℯ ∊ ⟨sym⟩.
Proof. simpl;tauto. Qed.
Lemma sym_b : 𝒷 ∊ ⟨sym⟩.
Proof. simpl;tauto. Qed.

Lemma sym_1 : 𝟭 ≲ ⟨sym⟩.
Proof. intros b ->;simpl;tauto. Qed.

Lemma sym_inf_seq B : B ≲ ⟨sym⟩ -> B⋅B≃B.
Proof.
  intros hB u;split.
  - intros (u1&u2&->&I1&I2).
    destruct u1 as [| |n' n],u2 as [| |m' m];simpl in I1,I2;try tauto.
    pose proof (hB _ I1) as E1.
    pose proof (hB _ I2) as E2.
    simpl in E1,E2;subst.
    unfold prod,SeqBind;simpl.
    destruct (Compare_dec.le_lt_dec n m) as [l|l].
    + rewrite <- (Minus.le_plus_minus _ _ l).
      apply PeanoNat.Nat.sub_0_le in l as ->;simpl.
      rewrite <- plus_n_O;assumption.
    + cut (m <= n);[clear l;intro l|lia].
      rewrite <- (Minus.le_plus_minus _ _ l).
      apply PeanoNat.Nat.sub_0_le in l as ->;simpl.
      rewrite <- plus_n_O;assumption.
  - intros I;exists u,u;simpl;repeat split;auto.
    apply hB in I.
    destruct u as [| |n' n];simpl in I;tauto||subst.
    unfold prod,SeqBind;simpl.
    rewrite <- Minus.le_plus_minus;[reflexivity|lia].
Qed.

Lemma sym_seq : ⟨sym⟩⋅⟨sym⟩≃⟨sym⟩.
Proof. apply sym_inf_seq;reflexivity. Qed.

Lemma star_inf_sym B : B ≲ ⟨sym⟩ -> B⋆ ≃ 𝟭 ∪ B.
Proof.
  intros h u;split.
  - intros (n&In).
    revert u In;induction n.
    + intros u ->;left;reflexivity.
    + intros u (u1&u2&->&I1&I2).
      apply IHn in I2 as [->|I2].
      * right;rewrite right_unit;assumption.
      * right;rewrite <- sym_inf_seq by assumption.
        exists u1,u2;auto.
  - intros [->|I].
    + exists 0;reflexivity.
    + exists 1,u,ℯ;rewrite right_unit;repeat split;auto.
Qed.
  
Lemma sym_star : ⟨sym⟩⋆≃⟨sym⟩.
Proof.
  rewrite star_inf_sym by reflexivity.
  symmetry;apply SetBiKA_inf_is_impl;intros ? ->;apply sym_e.
Qed.

Lemma finite_down_closed B1 B2 : B1 ≲ B2 -> finite B2 -> finite B1.
Proof.
  intros I (L&N&F).
  exists L;split;[assumption|].
  rewrite I;assumption.
Qed.

Lemma explicit_power n m k : Bnd n m ^ (S k) = Bnd (n + k*(n-m)) (m+k*(m-n)).
Proof.
  induction k;simpl.
  - repeat rewrite <-plus_n_O;reflexivity.
  - simpl in *;rewrite IHk;clear IHk;unfold prod,SeqBind;f_equal.
    + simpl.
      destruct (Compare_dec.le_lt_dec m n) as [l|l].
      * lia.
      * replace (n-m) with 0 by lia;simpl.
        rewrite PeanoNat.Nat.mul_0_r;simpl;lia.
    + simpl.
      destruct (Compare_dec.le_lt_dec m n) as [l|l].
      * replace (m-n) with 0 by lia;simpl.
        rewrite PeanoNat.Nat.mul_0_r;simpl;lia.
      * replace (n-m) with 0 by lia;simpl.
        rewrite PeanoNat.Nat.mul_0_r;simpl;lia.
Qed.

Lemma finite_star B : finite (B⋆) -> B ≲ ⟨sym⟩.
Proof.
  intros F b Ib.
  destruct b as [| |n m];simpl;auto.
  - destruct F as (L&E&I);apply E,I;exists 1,↯,ℯ;repeat split;assumption.
  - destruct_eqX n m;[reflexivity|exfalso].
    cut (unbounded (B⋆));[intros U;apply unbounded_not_finite in U;tauto|clear F].
    right;intros K;exists (Bnd n m ^ (S K));split.
    + exists (S K);generalize dependent (Bnd n m);clear;intros b Ib;induction (S K);simpl;auto.
      exists b,(b^n);auto.
    + clear Ib.
      rewrite explicit_power;simpl. 
      induction K.
      * rsimpl;lia.
      * rsimpl in *;lia.
Qed.

Lemma balanced_sym : ⟨balanced⟩ ≲ ⟨sym⟩.
Proof. intros [| |[] []];simpl;try tauto. Qed. 
Lemma balanced_finite : finite ⟨balanced⟩.
Proof.
  exists [ℯ;𝒷];simpl;split.
  - firstorder discriminate.
  - intros [| |[] []];simpl;try tauto.
Qed.

Lemma unbounded_seq B1 B2 : unbounded B1 -> unbounded B2 -> unbounded (B1⋅B2).
Proof.
  intros U1 [I2|U2];[|destruct (U2 0) as (b&Ib&_)];eapply unbounded_seq_left;eauto.
Qed.

Lemma unbounded_par B1 B2 : unbounded B1 -> unbounded B2 -> unbounded (B1∥B2).
Proof.
  intros [I1|U1];[|destruct (U1 1) as (b1&Ib1&S1)];
    (intros [I2|U2];[|destruct (U2 1) as (b2&Ib2&S2)]);left.
  - exists ↯,↯;auto.
  - exists ↯,b2;auto.
  - exists b1,↯;rewrite right_absorbing;auto.
  - exists b1,b2;repeat split;auto.
    destruct b1 as [| |n1 m1],b2 as [| |n2 m2];rsimpl in *;try reflexivity||lia.
    destruct n1,m1,n2,m2;try reflexivity||lia.
Qed.

Lemma unbounded_up_closed B1 B2 : B1 ≲ B2 -> unbounded B1 -> unbounded B2.
Proof.
  intros I [I1|U1].
  - left;apply I,I1.
  - right;intros N;destruct (U1 N) as (b&Ib&Sb);exists b;split;[apply I|];assumption.
Qed.

Lemma unbounded_union B1 B2 : unbounded B1 -> unbounded B2 -> unbounded (B1 ∪ B2).
Proof.
  intros U1 U2;eapply unbounded_up_closed;eauto.
  intros b Ib;right;assumption.
Qed.

Lemma unbounded_star B : unbounded B -> unbounded (B⋆).
Proof.
  apply unbounded_up_closed.
  intros b Ib;exists 1,b,ℯ;rewrite right_unit;repeat split;auto.
Qed.

