Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools algebra Bool bindings types_of_bsp.

Section s.
  Context {X : Set}.

  Inductive sp_terms {X : Set} : Set :=
    | sp_seq : sp_terms -> sp_terms -> sp_terms
    | sp_par : sp_terms -> sp_terms -> sp_terms
    | sp_var : X -> sp_terms
    | sp_unit : sp_terms.

  Global Instance sp_seq_prod : Product (@sp_terms X) := sp_seq.

  Global Instance sp_par_prod : ParProduct (@sp_terms X) := sp_par.

  Global Instance sp_unit_unit : Un (@sp_terms X) := sp_unit.

  Global Instance sp_size : Size (@sp_terms X) :=
    fix sp_size s :=
    match s with
    | sp_par s1 s2 | sp_seq s1 s2 => sp_size s1 + sp_size s2
    | sp_unit => 0
    | sp_var _ => 1
    end.

  Remark sp_unit_un : sp_unit = @un sp_terms _.
  Proof. reflexivity. Qed.
  Remark sp_size_un : ⎢𝟭⎥ = 0.
  Proof. reflexivity. Qed.
  Remark sp_size_var x : ⎢sp_var x⎥ = 1.
  Proof. reflexivity. Qed.
  Remark sp_prod_prod s t: sp_seq s t= (@prod sp_terms _ s t).
  Proof. reflexivity. Qed.
  Remark sp_size_prod s t : ⎢s⋅t⎥ = ⎢s⎥+⎢t⎥.
  Proof. reflexivity. Qed.
  Remark sp_par_par s t : sp_par s t = (@par sp_terms _ s t).
  Proof. reflexivity. Qed.
  Remark sp_size_par s t : ⎢s∥t⎥ = ⎢s⎥+⎢t⎥.
  Proof. reflexivity. Qed.
  
  Hint Rewrite sp_unit_un sp_size_un sp_size_var sp_prod_prod sp_size_prod sp_par_par sp_size_par : simpl_typeclasses.

  Inductive sp_eq : Equiv sp_terms :=
  | sp_eq_refl s : s ≡ s
  | sp_eq_sym s t : s ≡ t -> t ≡ s
  | sp_eq_trans s t u : s ≡ t -> t ≡ u -> s ≡ u
  | sp_eq_seq s t s' t' : s ≡ t -> s' ≡ t' -> s ⋅ s' ≡ t ⋅ t'
  | sp_eq_par s t s' t' : s ≡ t -> s' ≡ t' -> s ∥ s' ≡ t ∥ t'
  | sp_eq_seq_ass s t u : s ⋅ (t ⋅ u) ≡ (s ⋅ t) ⋅ u
  | sp_eq_par_ass s t u : s ∥ (t ∥ u) ≡ (s ∥ t) ∥ u
  | sp_eq_par_comm s t : s ∥ t ≡ t ∥ s
  | sp_eq_seq_left_unit s : 𝟭 ⋅ s ≡ s
  | sp_eq_seq_right_unit s : s ⋅ 𝟭 ≡ s
  | sp_eq_par_unit s : 𝟭 ∥ s ≡ s.
  Hint Constructors sp_eq.
  Global Instance sp_eq_Equiv : Equiv sp_terms := sp_eq.

  Global Instance sp_eq_Equivalence : Equivalence equiv.
  Proof. split;intro;intros;eauto. Qed.

  Global Instance sp_terms_bimonoid : BiMonoid sp_terms equiv prod par un.
  Proof. repeat split;repeat intro;eauto. Qed.

  Lemma sp_size_proper : Proper (equiv ==> Logic.eq) size.
  Proof. intros s t E;induction E;rsimpl;lia. Qed.

  Lemma sp_size_unit s : ⎢s⎥ = 0 <-> s ≡ 𝟭.
  Proof.
    split.
    - induction s;rsimpl.
      + intro;rewrite IHs1,IHs2;auto||lia.
      + intro;rewrite IHs1,IHs2;auto||lia.
      + discriminate.
      + reflexivity.
    - intros E;apply sp_size_proper in E as ->;reflexivity.
  Qed.
  Fixpoint sp_clean s :=
    match s with
    | sp_par s1 s2 =>
      match sp_clean s1,sp_clean s2 with
      | sp_unit,s' | s',sp_unit => s'
      | s'1,s'2 => s'1∥s'2
      end
    | sp_seq s1 s2 =>
      match sp_clean s1,sp_clean s2 with
      | sp_unit,s' | s',sp_unit => s'
      | s'1,s'2 => s'1⋅s'2
      end
    | s => s
    end.

  Lemma sp_clean_eq s : s ≡ sp_clean s.
  Proof.
    induction s;simpl.
    - destruct (sp_clean s1),(sp_clean s2);rewrite IHs1,IHs2;auto;
        rewrite left_unit||rewrite right_unit;reflexivity.
    - destruct (sp_clean s1),(sp_clean s2);rewrite IHs1,IHs2;auto;
        rewrite left_unit||rewrite right_unit;reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Fixpoint is_sp_clean (s : @sp_terms X) :=
    match s with
    | sp_par s1 s2 | sp_seq s1 s2 => is_sp_clean s1 /\ is_sp_clean s2
    | sp_var _ => True
    | _ => False
    end.

  Lemma sp_clean_idem s : is_sp_clean s -> sp_clean s = s.
  Proof.
    induction s;simpl.
    - intros (C1&C2).
      rewrite (IHs1 C1) in *;rewrite (IHs2 C2) in *.
      destruct s1,s2;simpl in *;reflexivity||tauto.
    - intros (C1&C2).
      rewrite (IHs1 C1) in *;rewrite (IHs2 C2) in *.
      destruct s1,s2;simpl in *;reflexivity||tauto.
    - reflexivity.
    - tauto.
  Qed.

  Lemma sp_clean_is_sp_clean s : sp_clean s = 𝟭 \/ is_sp_clean (sp_clean s).
  Proof.
    induction s.
    - simpl;destruct IHs1 as [->|I1],IHs2 as [->|I2];simpl;auto.
      + destruct (sp_clean s1);simpl in *;auto.
      + destruct (sp_clean s1),(sp_clean s2);simpl in *;auto.
    - simpl;destruct IHs1 as [->|I1],IHs2 as [->|I2];simpl;auto.
      + destruct (sp_clean s1);simpl in *;auto.
      + destruct (sp_clean s1),(sp_clean s2);simpl in *;auto.
    - right;simpl;auto.
    - left;reflexivity.
  Qed.

  Lemma is_sp_clean_sp_size s : is_sp_clean s -> 0 < ⎢s⎥.
  Proof. induction s;rsimpl;firstorder lia. Qed.

  Definition sp_type t :=
    match sp_clean t with
    | sp_var _ => VarT
    | sp_seq _ _ => SeqT
    | sp_par _ _ => ParT
    | sp_unit => UnT
    end.
  
  Lemma sp_type_clean_proper : Proper (equiv ==> Logic.eq) (fun s => sp_type s).
  Proof.
    intros s t E;induction E;simpl;auto.
    - etransitivity;eassumption.
    - unfold sp_type in *;simpl in *;
        destruct (sp_clean s),(sp_clean t);simpl in *;try discriminate;
          destruct (sp_clean s'),(sp_clean t');simpl in *;discriminate||reflexivity.
    - unfold sp_type in *;simpl in *;
        destruct (sp_clean s),(sp_clean t);simpl in *;try discriminate;
          destruct (sp_clean s'),(sp_clean t');simpl in *;discriminate||reflexivity.
    - unfold sp_type in *;simpl in *;
        destruct (sp_clean s),(sp_clean t),(sp_clean u);simpl in *;discriminate||reflexivity.
    - unfold sp_type in *;simpl in *;
        destruct (sp_clean s),(sp_clean t),(sp_clean u);simpl in *;discriminate||reflexivity.
    - unfold sp_type in *;simpl in *;
        destruct (sp_clean s),(sp_clean t);simpl in *;discriminate||reflexivity.
    - unfold sp_type in *;simpl in *;
        destruct (sp_clean s);simpl in *;discriminate||reflexivity.
  Qed.
  
  Lemma sp_size_Π L : ⎢Π L⎥ = sum size L.
  Proof. induction L;rsimpl;auto. Qed.
  
  Fixpoint subterms (s : @sp_terms X) :=
    match s with
    | sp_par s1 s2 | sp_seq s1 s2 => s::subterms s1 ++ subterms s2
    | s => [s]
    end.
  
  Context {dec: decidable_set X}.
  Global Instance dec_sp_terms : decidable_set (@sp_terms X).
  Proof.
    set (sp_eqX := fix f s t := match s,t with
                             | sp_unit,sp_unit => true
                             | sp_var x,sp_var y => x =?= y
                             | sp_seq s1 s2,sp_seq t1 t2
                             | sp_par s1 s2,sp_par t1 t2 => f s1 t1 && f s2 t2
                             | _,_ => false
                             end).
    apply (@Build_decidable_set sp_terms sp_eqX).
    intros s t;apply iff_reflect.
    revert t;induction s as [s1 ? s2|s1 ? s2|x|];intros [t1 t2|t1 t2|y|];simpl;
      repeat rewrite andb_true_iff;try rewrite <-IHs1,<-IHs2;
        firstorder (try discriminate||inversion H;subst;auto).
    - apply eqX_correct;reflexivity.
    - rewrite eqX_correct in H;subst;reflexivity.
  Qed.
  
  Axiom sp_eq_dec : forall s t, {s ≡ t} + {~ (s ≡ t)}.
  
End s.
Arguments sp_terms : clear implicits.
Hint Constructors sp_eq.
Hint Rewrite @sp_size_un @sp_size_var @sp_prod_prod @sp_size_prod @sp_par_par @sp_size_par : simpl_typeclasses.
  
