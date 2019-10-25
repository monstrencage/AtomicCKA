Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools algebra Bool bindings types_of_bsp.
Require Export sp_terms brackets.

Section brack_terms.
  Context {X : Set} {decX : decidable_set X}.
  
  Notation " ⦃ " := (sp_var (inr Open)).
  Notation " ⦄ " := (sp_var (inr Close)).
  Notation VOpen := (sp_var (inr Open)).
  Notation VClose := (sp_var (inr Close)).
  Notation X' := (X + brack)%type.

  Fixpoint sp_bind (s : sp_terms X') : binding :=
    match s with
    | sp_seq s1 s2 => sp_bind s1 ⋅ sp_bind s2
    | sp_par s1 s2 => sp_bind s1 ∥ sp_bind s2
    | sp_var (inl x) => 𝒷
    | ⦃ => ℴ | ⦄ => 𝒸
    | sp_unit => ℯ
    end.

  Global Instance sp_bind_proper : Proper (equiv ==> Logic.eq) sp_bind.
  Proof.
    intros s t E;induction E;simpl;auto.
    - rewrite IHE;assumption.
    - rewrite IHE,IHE0;reflexivity.
    - rewrite IHE,IHE0;reflexivity.
    - apply mon_assoc.
    - apply mon_assoc.
    - apply bimon_comm.
    - apply left_unit.
    - apply right_unit.
    - apply left_unit.
  Qed.

  Lemma sp_binding_unit s : sp_bind s = ℯ <-> s ≡ 𝟭.
  Proof.
    split;[|intros ->;reflexivity].
    induction s;simpl;auto.
    - destruct (sp_bind s1),(sp_bind s2);try discriminate.
      rewrite IHs1,IHs2 by reflexivity.
      intros _;apply left_unit.
    - destruct (sp_bind s1),(sp_bind s2);try discriminate.
      + rewrite IHs1,IHs2 by reflexivity.
        intros _;apply left_unit.
      + destruct n,n0;discriminate.
      + destruct n,n0;discriminate.
      + destruct n,n0,n1,n2;discriminate.
    - destruct x as [|[]];discriminate.
  Qed.
  
  Lemma sp_clean_not_unit s : is_sp_clean s -> sp_bind s <> ℯ.
  Proof.
    intro C;apply is_sp_clean_sp_size in C.
    rewrite sp_binding_unit,<-sp_size_unit.
    lia.
  Qed.

  Lemma bind_error_par a b :
    (a ∥ b) <> ↯ -> (a <> ↯ /\ b <> ↯).
  Proof. intros N;split;intros ->;apply N;[apply left_absorbing|apply right_absorbing]. Qed.

  Lemma sp_bind_par_correct s t :
    is_sp_clean s -> is_sp_clean t -> 
    (sp_bind s ∥ sp_bind t) <> ↯ <-> (sp_bind s = 𝒷 /\ sp_bind t = 𝒷).
  Proof.
    intros C1 C2;apply sp_clean_not_unit in C1;apply sp_clean_not_unit in C2.
    destruct (sp_bind s) as [| |[] []],(sp_bind t) as [| |[] []];
      try (exfalso;apply C1;reflexivity)||(exfalso;apply C2;reflexivity)
      ||rewrite left_absorbing||rewrite right_absorbing;
      try (split;[tauto|intros (E&E');discriminate]).
  Qed.

  Lemma sp_bind_par_not_nil s t x :
    is_sp_clean s -> is_sp_clean t -> 
    (sp_bind s ∥ sp_bind t) ⋅ x <> ↯ -> (sp_bind s = 𝒷 /\ sp_bind t = 𝒷).
  Proof.
    intros C1 C2;apply sp_clean_not_unit in C1;apply sp_clean_not_unit in C2.
    destruct (sp_bind s) as [| |[] []],(sp_bind t) as [| |[] []];
      try (exfalso;apply C1;reflexivity)||(exfalso;apply C2;reflexivity)
      ||rewrite left_absorbing;tauto.
  Qed.

  Definition open b := match b with Bnd _ n => n | _ => 0 end.
  Definition close b := match b with Bnd n _ => n | _ => 0 end.

  Lemma open_prod a b : a⋅b <> ↯ -> open (a ⋅ b) = open b + (open a - close b).
  Proof. destruct a as [| |ca oa],b as [| |cb ob];simpl;lia||tauto. Qed.
  Lemma close_prod a b : a⋅b <> ↯ -> close (a ⋅ b) = close a + (close b - open a).
  Proof. destruct a as [| |ca oa],b as [| |cb ob];simpl;lia||tauto. Qed.

  Lemma bind_error_seq a b : a⋅b = ↯ <-> a = ↯ \/ b = ↯.
  Proof. destruct a as [| |ca oa],b as [| |cb ob];split;firstorder discriminate. Qed.

    Lemma sp_clean_dec_par (s t : sp_terms X') :
    (sp_clean s = 𝟭 /\ sp_clean t = 𝟭 /\ sp_clean (s∥t) = 𝟭)
    \/  (sp_clean s = 𝟭 /\ is_sp_clean (sp_clean t) /\ sp_clean (s∥t) = sp_clean t)
    \/  (is_sp_clean (sp_clean s) /\ sp_clean t = 𝟭 /\ sp_clean (s∥t) = sp_clean s)
    \/  (is_sp_clean (sp_clean s) /\ is_sp_clean (sp_clean t)
        /\ sp_clean (s∥t) = sp_clean s ∥sp_clean t).
  Proof.
    simpl;destruct (sp_clean_is_sp_clean s) as [->|Cs];
      destruct (sp_clean_is_sp_clean t) as [->|Ct];simpl;auto.
    - right;right;left.
      split;[|split];auto.
      destruct (sp_clean s);auto.
    - repeat right.
      split;[|split];auto.
      destruct (sp_clean s),(sp_clean t);simpl in *;reflexivity||tauto.
  Qed.

  Lemma sp_clean_par_left (s t : sp_terms X') :
    sp_clean t = 𝟭 -> sp_clean (s∥t) = sp_clean s.
  Proof. intros h2;simpl;rewrite h2;destruct (sp_clean s);reflexivity. Qed.
  Lemma sp_clean_par_right (s t : sp_terms X') :
    sp_clean s = 𝟭 -> sp_clean (s∥t) = sp_clean t.
  Proof. simpl;intros ->;reflexivity. Qed.
  Lemma sp_clean_par_clean (s t : sp_terms X') :
    is_sp_clean (sp_clean s) -> is_sp_clean (sp_clean t) ->
    sp_clean (s∥t) = sp_clean s ∥ sp_clean t.
  Proof.
    simpl;intros h1 h2;destruct (sp_clean s),(sp_clean t);
      reflexivity||(exfalso;revert h1 h2;simpl;tauto).
  Qed.
  Lemma sp_clean_seq_left (s t : sp_terms X') :
    sp_clean t = 𝟭 -> sp_clean (s⋅t) = sp_clean s.
  Proof. intros h2;simpl;rewrite h2;destruct (sp_clean s);reflexivity. Qed.
  Lemma sp_clean_seq_right (s t : sp_terms X') :
    sp_clean s = 𝟭 -> sp_clean (s⋅t) = sp_clean t.
  Proof. simpl;intros ->;reflexivity. Qed.
  Lemma sp_clean_seq_clean (s t : sp_terms X') :
    is_sp_clean (sp_clean s) -> is_sp_clean (sp_clean t) ->
    sp_clean (s⋅t) = sp_clean s ⋅ sp_clean t.
  Proof.
    simpl;intros h1 h2;destruct (sp_clean s),(sp_clean t);
      reflexivity||(exfalso;revert h1 h2;simpl;tauto).
  Qed.

End brack_terms.
Notation VOpen := (sp_var (inr Open)).
Notation VClose := (sp_var (inr Close)).

