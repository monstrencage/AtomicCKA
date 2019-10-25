Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools algebra Bool bindings types_of_bsp notations.
  
Section b.
  Context {X : Set}.

  Inductive bsp_terms {X:Set} : Set :=
    | bsp_seq : bsp_terms -> bsp_terms -> bsp_terms
    | bsp_par : bsp_terms -> bsp_terms -> bsp_terms
    | bsp_var : X -> bsp_terms
    | bsp_box : bsp_terms -> bsp_terms
    | bsp_unit : bsp_terms.

  Global Instance bsp_seq_prod : Product (@bsp_terms X) := bsp_seq.

  Global Instance bsp_par_prod : ParProduct (@bsp_terms X) := bsp_par.

  Global Instance bsp_unit_unit : Un (@bsp_terms X) := bsp_unit.

  Global Instance bsp_box_Box : Box (@bsp_terms X) := bsp_box.

  Global Instance bsp_size : Size (@bsp_terms X) :=
    fix bsp_size s :=
    match s with
    | bsp_par s1 s2 | bsp_seq s1 s2 => bsp_size s1 + bsp_size s2
    | bsp_box s => bsp_size s
    | bsp_unit => 0
    | bsp_var _ => 1
    end.
  
  Remark bsp_unit_un : bsp_unit = @un bsp_terms _.
  Proof. reflexivity. Qed.
  Remark bsp_size_un : ⎢𝟭⎥ = 0.
  Proof. reflexivity. Qed.
  Remark bsp_size_var x : ⎢bsp_var x⎥ = 1.
  Proof. reflexivity. Qed.
  Remark bsp_box_box s : bsp_box s = (@box bsp_terms _ s).
  Proof. reflexivity. Qed.
  Remark bsp_size_box s : ⎢▢ s⎥ = ⎢s⎥.
  Proof. reflexivity. Qed.
  Remark bsp_prod_prod s t : bsp_seq s t = (@prod bsp_terms _ s t).
  Proof. reflexivity. Qed.
  Remark bsp_size_prod s t : ⎢s⋅t⎥ = ⎢s⎥+⎢t⎥.
  Proof. reflexivity. Qed.
  Remark bsp_par_par s t : bsp_par s t = (@par bsp_terms _ s t).
  Proof. reflexivity. Qed.
  Remark bsp_size_par s t : ⎢s∥t⎥ = ⎢s⎥+⎢t⎥.
  Proof. reflexivity. Qed.
  
  Hint Rewrite bsp_unit_un bsp_size_un bsp_size_var bsp_prod_prod bsp_size_prod bsp_par_par bsp_size_par bsp_box_box bsp_size_box: simpl_typeclasses.

  Inductive bsp_eq : Equiv bsp_terms :=
  | bsp_eq_refl s : s ≡ s
  | bsp_eq_sym s t : s ≡ t -> t ≡ s
  | bsp_eq_trans s t u : s ≡ t -> t ≡ u -> s ≡ u
  | bsp_eq_seq s t s' t' : s ≡ t -> s' ≡ t' -> s ⋅ s' ≡ t ⋅ t'
  | bsp_eq_par s t s' t' : s ≡ t -> s' ≡ t' -> s ∥ s' ≡ t ∥ t'
  | bsp_eq_box s t : s ≡ t -> ▢ s ≡ ▢ t
  | bsp_eq_seq_ass s t u : s ⋅ (t ⋅ u) ≡ (s ⋅ t) ⋅ u
  | bsp_eq_par_ass s t u : s ∥ (t ∥ u) ≡ (s ∥ t) ∥ u
  | bsp_eq_par_comm s t : s ∥ t ≡ t ∥ s
  | bsp_eq_seq_left_unit s : 𝟭 ⋅ s ≡ s
  | bsp_eq_seq_right_unit s : s ⋅ 𝟭 ≡ s
  | bsp_eq_par_unit s : 𝟭 ∥ s ≡ s
  | bsp_eq_box_box s : ▢ (▢ s) ≡ ▢ s
  | bsp_eq_box_unit : ▢ 𝟭 ≡ 𝟭.
  
  Hint Constructors bsp_eq.
  Global Instance bsp_eq_Equiv : Equiv bsp_terms := bsp_eq.

  Global Instance bsp_eq_Equivalence : Equivalence equiv.
  Proof. split;intro;intros;eauto. Qed.

  Global Instance bsp_terms_bimonoid : BiMonoid bsp_terms equiv prod par un.
  Proof. repeat split;repeat intro;eauto. Qed.

  Global Instance bsp_box_proper : Proper (equiv ==> equiv) ▢.
  Proof. intros e f E;auto. Qed.

  Lemma bsp_size_proper : Proper (equiv ==> Logic.eq) size.
  Proof. intros s t E;induction E;reflexivity||(rsimpl;lia). Qed.
  
  Lemma bsp_size_unit s : ⎢s⎥ = 0 <-> s ≡ 𝟭.
  Proof.
    split.
    - induction s;rsimpl.
      + intro;rewrite IHs1,IHs2;auto||lia.
      + intro;rewrite IHs1,IHs2;auto||lia.
      + discriminate.
      + intro;rewrite IHs;auto.
      + reflexivity.
    - intros E;apply bsp_size_proper in E as ->;reflexivity.
  Qed.

  Fixpoint bsp_clean s :=
    match s with
    | bsp_par s1 s2 =>
      match bsp_clean s1,bsp_clean s2 with
      | bsp_unit,s' | s',bsp_unit => s'
      | s'1,s'2 => s'1∥s'2
      end
    | bsp_seq s1 s2 =>
      match bsp_clean s1,bsp_clean s2 with
      | bsp_unit,s' | s',bsp_unit => s'
      | s'1,s'2 => s'1⋅s'2
      end
    | bsp_box s =>
      match bsp_clean s with
      | bsp_box s' => ▢ s'
      | bsp_unit => bsp_unit
      | s' => ▢ s'
      end
    | s => s
    end.

  Lemma bsp_clean_eq s : s ≡ bsp_clean s.
  Proof.
    induction s;simpl.
    - destruct (bsp_clean s1),(bsp_clean s2);rewrite IHs1,IHs2;auto;
        rewrite left_unit||rewrite right_unit;reflexivity.
    - destruct (bsp_clean s1),(bsp_clean s2);rewrite IHs1,IHs2;auto;
        rewrite left_unit||rewrite right_unit;reflexivity.
    - reflexivity.
    - destruct (bsp_clean s); rewrite IHs;rsimpl;auto.
    - reflexivity.
  Qed.

  Fixpoint is_bsp_clean (s : @bsp_terms X) :=
    match s with
    | bsp_par s1 s2 | bsp_seq s1 s2 => is_bsp_clean s1 /\ is_bsp_clean s2
    | bsp_var _ => True
    | bsp_box (bsp_box _) => False
    | bsp_box s => is_bsp_clean s
    | _ => False
    end.

  Lemma bsp_clean_is_bsp_clean s : bsp_clean s = 𝟭 \/ is_bsp_clean (bsp_clean s).
  Proof.
    induction s.
    - simpl;destruct IHs1 as [->|I1],IHs2 as [->|I2];simpl;auto.
      + destruct (bsp_clean s1);simpl in *;auto.
      + destruct (bsp_clean s1),(bsp_clean s2);simpl in *;auto.
    - simpl;destruct IHs1 as [->|I1],IHs2 as [->|I2];simpl;auto.
      + destruct (bsp_clean s1);simpl in *;auto.
      + destruct (bsp_clean s1),(bsp_clean s2);simpl in *;auto.
    - right;simpl;auto.
    - simpl;destruct IHs as [->|I];simpl;auto.
      destruct (bsp_clean s);simpl in *;auto.
    - left;reflexivity.
  Qed.

  Lemma is_bsp_clean_bsp_size s : is_bsp_clean s -> 0 < ⎢s⎥.
  Proof.
    induction s;rsimpl;try firstorder lia.
    destruct s;firstorder lia.
  Qed.
        
  Reserved Notation " a ⩳ b " (at level 80).
  Inductive bsp_eq_bis : relation bsp_terms :=
  | bsp_eq_bis_refl s : s ⩳ s
  | bsp_eq_bis_sym s t : s ⩳ t -> t ⩳ s
  | bsp_eq_bis_trans s t u : is_bsp_clean t -> s ⩳ t -> t ⩳ u -> s ⩳ u
  | bsp_eq_bis_seq s t s' t' : s ⩳ t -> s' ⩳ t' -> s ⋅ s' ⩳ t ⋅ t'
  | bsp_eq_bis_par s t s' t' : s ⩳ t -> s' ⩳ t' -> s ∥ s' ⩳ t ∥ t'
  | bsp_eq_bis_box s t : s ⩳ t -> ▢ s ⩳ ▢ t
  | bsp_eq_bis_seq_ass s t u : s ⋅ (t ⋅ u) ⩳ (s ⋅ t) ⋅ u
  | bsp_eq_bis_par_ass s t u : s ∥ (t ∥ u) ⩳ (s ∥ t) ∥ u
  | bsp_eq_bis_par_comm s t : s ∥ t ⩳ t ∥ s
  where " a ⩳ b " := (bsp_eq_bis a b).
  Hint Constructors bsp_eq_bis.
  
  Global Instance bsp_eq_bis_equiv : subrelation bsp_eq_bis equiv.
  Proof. intros s t E;induction E;simpl;eauto. Qed.

  Definition bsp_type (t : @bsp_terms X) :=
    match t with
    | bsp_var _ => VarT
    | bsp_seq _ _ => SeqT
    | bsp_par _ _ => ParT
    | bsp_box _ => BoxT
    | bsp_unit => UnT
    end.

  Lemma bsp_type_proper : Proper (bsp_eq_bis ==> Logic.eq) bsp_type.
  Proof.
    intros s t E;induction E;simpl;try reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
  Qed.

  Fixpoint bsp_height (t : @bsp_terms X) :=
    match t with
    | bsp_seq t1 t2 | bsp_par t1 t2 => bsp_height t1 ⊕ bsp_height t2
    | bsp_box t => 1 + bsp_height t
    | _ => 0
    end.

  Lemma bsp_height_proper_bis : Proper (bsp_eq_bis ==> Logic.eq) bsp_height.
  Proof. intros s t E;induction E;simpl;lia||auto. Qed.

  Lemma bsp_eq_bis_is_bsp_clean : Proper (bsp_eq_bis ==> iff) is_bsp_clean.
  Proof.
    intros s t E;induction E;simpl;try tauto.
    destruct s,t;simpl in *;tauto||auto.
    - apply bsp_type_proper in E;simpl in E;discriminate.
    - apply bsp_type_proper in E;simpl in E;discriminate.
    - apply bsp_height_proper_bis in E;simpl in E;discriminate.
    - apply bsp_type_proper in E;simpl in E;discriminate.
    - apply bsp_type_proper in E;simpl in E;discriminate.
    - apply bsp_height_proper_bis in E;simpl in E;discriminate.
  Qed.
  
  Corollary bsp_eq_bis_is_one s : s ⩳ 𝟭 -> s = 𝟭.
  Proof.
    cut (forall t, s ⩳ t -> s = 𝟭 <-> t = 𝟭);[intros hyp E;apply (hyp _ E);reflexivity|].
    intros t E;induction E;try tauto.
    - split;discriminate.
    - split;discriminate.
    - split;discriminate.
    - split;discriminate.
    - split;discriminate.
    - split;discriminate.
  Qed.

  Lemma bsp_clean_seq_1_1 s t :
    bsp_clean s = 𝟭 -> bsp_clean t = 𝟭 -> bsp_clean (s⋅t) = 𝟭.
  Proof. simpl;intros -> -> ;reflexivity. Qed.
  Lemma bsp_clean_seq_1r s t :
    bsp_clean t = 𝟭 -> bsp_clean (s⋅t) = bsp_clean s.
  Proof. simpl;intros -> ;simpl;destruct (bsp_clean s);reflexivity. Qed.
  Lemma bsp_clean_seq_1l s t :
    bsp_clean s = 𝟭 -> bsp_clean (s⋅t) = bsp_clean t.
  Proof. simpl;intros ->;simpl; destruct (bsp_clean t);reflexivity. Qed.
  Lemma bsp_clean_seq_clean s t :
    is_bsp_clean (bsp_clean s) -> is_bsp_clean (bsp_clean t) ->
    bsp_clean (s⋅t) = bsp_clean s⋅bsp_clean t.
  Proof.
    simpl;intros C1 C2.
    destruct (bsp_clean s);
      (exfalso;apply C1)||(destruct (bsp_clean t));
      reflexivity||(exfalso;apply C2).
  Qed.
      
  Lemma bsp_clean_par_1_1 s t :
    bsp_clean s = 𝟭 -> bsp_clean t = 𝟭 -> bsp_clean (s∥t) = 𝟭.
  Proof. simpl;intros -> -> ;reflexivity. Qed.
  Lemma bsp_clean_par_1r s t :
    bsp_clean t = 𝟭 -> bsp_clean (s∥t) = bsp_clean s.
  Proof. simpl;intros -> ;simpl;destruct (bsp_clean s);reflexivity. Qed.
  Lemma bsp_clean_par_1l s t :
    bsp_clean s = 𝟭 -> bsp_clean (s∥t) = bsp_clean t.
  Proof. simpl;intros ->;simpl; destruct (bsp_clean t);reflexivity. Qed.
  Lemma bsp_clean_par_clean s t :
    is_bsp_clean (bsp_clean s) -> is_bsp_clean (bsp_clean t) ->
    bsp_clean (s∥t) = bsp_clean s∥bsp_clean t.
  Proof.
    simpl;intros C1 C2.
    destruct (bsp_clean s);
      (exfalso;apply C1)||(destruct (bsp_clean t));
      reflexivity||(exfalso;apply C2).
  Qed.
      
  Lemma bsp_clean_proper : Proper (equiv ==> bsp_eq_bis) bsp_clean.
  Proof.
    intros s t E;induction E;auto.
    - destruct (bsp_clean_is_bsp_clean t) as [Et|C].
      + rewrite Et in *.
        apply bsp_eq_bis_sym in IHE0.
        apply bsp_eq_bis_is_one in IHE as ->.
        apply bsp_eq_bis_is_one in IHE0 as ->.
        auto.
      + apply (bsp_eq_bis_trans C);assumption.
    - destruct (bsp_clean_is_bsp_clean s) as [Es|Cs],
                                             (bsp_clean_is_bsp_clean s') as [Es'|Cs'].
      + rewrite bsp_clean_seq_1_1 by assumption.
        rewrite bsp_clean_seq_1_1;auto.
        * rewrite Es in *.
          apply bsp_eq_bis_is_one,bsp_eq_bis_sym,IHE.
        * rewrite Es' in *.
          apply bsp_eq_bis_is_one,bsp_eq_bis_sym,IHE0.
      + rewrite bsp_clean_seq_1l by assumption.
        rewrite bsp_clean_seq_1l;auto.
        rewrite Es in *.
        apply bsp_eq_bis_is_one,bsp_eq_bis_sym,IHE.
      + rewrite bsp_clean_seq_1r by assumption.
        rewrite bsp_clean_seq_1r;auto.
        rewrite Es' in *.
        apply bsp_eq_bis_is_one,bsp_eq_bis_sym,IHE0.
      + rewrite bsp_clean_seq_clean by assumption.
        rewrite bsp_clean_seq_clean;auto.
        * apply (bsp_eq_bis_is_bsp_clean IHE),Cs.
        * apply (bsp_eq_bis_is_bsp_clean IHE0),Cs'.
    - destruct (bsp_clean_is_bsp_clean s) as [Es|Cs],
                                             (bsp_clean_is_bsp_clean s') as [Es'|Cs'].
      + rewrite bsp_clean_par_1_1 by assumption.
        rewrite bsp_clean_par_1_1;auto.
        * rewrite Es in *.
          apply bsp_eq_bis_is_one,bsp_eq_bis_sym,IHE.
        * rewrite Es' in *.
          apply bsp_eq_bis_is_one,bsp_eq_bis_sym,IHE0.
      + rewrite bsp_clean_par_1l by assumption.
        rewrite bsp_clean_par_1l;auto.
        rewrite Es in *.
        apply bsp_eq_bis_is_one,bsp_eq_bis_sym,IHE.
      + rewrite bsp_clean_par_1r by assumption.
        rewrite bsp_clean_par_1r;auto.
        rewrite Es' in *.
        apply bsp_eq_bis_is_one,bsp_eq_bis_sym,IHE0.
      + rewrite bsp_clean_par_clean by assumption.
        rewrite bsp_clean_par_clean;auto.
        * apply (bsp_eq_bis_is_bsp_clean IHE),Cs.
        * apply (bsp_eq_bis_is_bsp_clean IHE0),Cs'.
    - simpl;destruct (bsp_clean s),(bsp_clean t);
        try (apply bsp_type_proper in IHE;discriminate);
        auto.
    - destruct (bsp_clean_is_bsp_clean s) as [Es|Cs];
        destruct (bsp_clean_is_bsp_clean t) as [Et|Ct];
        destruct (bsp_clean_is_bsp_clean u) as [Eu|Cu];
        repeat (rewrite bsp_clean_seq_1_1 by assumption)
        ||(rewrite bsp_clean_seq_1l by assumption)
        ||(rewrite bsp_clean_seq_1r by assumption)
        ||(rewrite bsp_clean_seq_clean by (simpl;tauto));auto.
      + rewrite bsp_clean_seq_1l;auto.
        apply bsp_clean_seq_1_1;auto.
      + rewrite bsp_clean_seq_clean.
        * rewrite bsp_clean_seq_1l;auto.
        * rewrite bsp_clean_seq_1l;auto.
        * assumption.
      + repeat rewrite bsp_clean_seq_1r;auto.
      + rewrite bsp_clean_seq_clean;auto.
        * rewrite bsp_clean_seq_1l;auto.
          rewrite bsp_clean_seq_clean;auto.
          -- rewrite bsp_clean_seq_1r;auto.
          -- rewrite bsp_clean_seq_1r;auto.
        * rewrite bsp_clean_seq_1l;auto.
      + rewrite bsp_clean_seq_clean;auto.
        * rewrite bsp_clean_seq_1r;auto.
          rewrite bsp_clean_seq_1r;auto.
          rewrite bsp_clean_seq_clean;auto.
        * rewrite bsp_clean_seq_1r;auto.
      + repeat rewrite bsp_clean_seq_clean;simpl;auto.
    - destruct (bsp_clean_is_bsp_clean s) as [Es|Cs];
        destruct (bsp_clean_is_bsp_clean t) as [Et|Ct];
        destruct (bsp_clean_is_bsp_clean u) as [Eu|Cu];
        repeat (rewrite bsp_clean_par_1_1 by assumption)
        ||(rewrite bsp_clean_par_1l by assumption)
        ||(rewrite bsp_clean_par_1r by assumption)
        ||(rewrite bsp_clean_par_clean by (simpl;tauto));auto.
      + rewrite bsp_clean_par_1l;auto.
        apply bsp_clean_par_1_1;auto.
      + rewrite bsp_clean_par_clean.
        * rewrite bsp_clean_par_1l;auto.
        * rewrite bsp_clean_par_1l;auto.
        * assumption.
      + repeat rewrite bsp_clean_par_1r;auto.
      + rewrite bsp_clean_par_clean;auto.
        * rewrite bsp_clean_par_1l;auto.
          rewrite bsp_clean_par_clean;auto.
          -- rewrite bsp_clean_par_1r;auto.
          -- rewrite bsp_clean_par_1r;auto.
        * rewrite bsp_clean_par_1l;auto.
      + rewrite bsp_clean_par_clean;auto.
        * rewrite bsp_clean_par_1r;auto.
          rewrite bsp_clean_par_1r;auto.
          rewrite bsp_clean_par_clean;auto.
        * rewrite bsp_clean_par_1r;auto.
      + repeat rewrite bsp_clean_par_clean;simpl;auto.
    - destruct (bsp_clean_is_bsp_clean s) as [Es|Cs];
        destruct (bsp_clean_is_bsp_clean t) as [Et|Ct];
        repeat (rewrite bsp_clean_par_1_1 by assumption)
        ||(rewrite bsp_clean_par_1l by assumption)
        ||(rewrite bsp_clean_par_1r by assumption)
        ||(rewrite bsp_clean_par_clean by (simpl;tauto));auto.
    - rewrite bsp_clean_seq_1r by reflexivity;auto.
    - simpl;destruct (bsp_clean s);simpl;auto.
  Qed.
  
  Notation 𝒟 := (fun t => bsp_height (bsp_clean t)).

  Lemma bsp_height_proper : Proper (equiv ==> Logic.eq) 𝒟.
  Proof. intros s t E;apply bsp_height_proper_bis,bsp_clean_proper,E. Qed.

  Context {dec: decidable_set X}.
  Global Instance dec_bsp_terms : decidable_set (@bsp_terms X).
  Proof.
    set (bsp_eqX := fix f s t := match s,t with
                             | bsp_unit,bsp_unit => true
                             | bsp_var x,bsp_var y => x =?= y
                             | bsp_seq s1 s2,bsp_seq t1 t2
                             | bsp_par s1 s2,bsp_par t1 t2 => f s1 t1 && f s2 t2
                             | bsp_box s,bsp_box t => f s t
                             | _,_ => false
                             end).
    apply (@Build_decidable_set bsp_terms bsp_eqX).
    intros s t;apply iff_reflect.
    revert t;induction s as [s1 ? s2|s1 ? s2|x|s|];intros [t1 t2|t1 t2|y|t|];simpl;
      repeat rewrite andb_true_iff;try rewrite <-IHs1,<-IHs2;
        firstorder (try discriminate||inversion H;subst;auto).
    - apply eqX_correct;reflexivity.
    - rewrite eqX_correct in H;subst;reflexivity.
  Qed.

  Inductive term_subsumption : @Subsumption bsp_terms :=
  | subs_eq s t : s ≡ t -> s ⊑ t
  | subs_trans s t u : s ⊑ t -> t ⊑ u -> s ⊑ u
  | subs_seq s t s' t' : s ⊑ t -> s' ⊑ t' -> s ⋅ s' ⊑ t ⋅ t'
  | subs_par s t s' t' : s ⊑ t -> s' ⊑ t' -> s ∥ s' ⊑ t ∥ t'
  | subs_box s t : s ⊑ t -> ▢ s ⊑ ▢ t
  | subs_exchange a b c d : (a ∥ b) ⋅ (c ∥ d) ⊑ (a ⋅ c) ∥ (b ⋅ d)
  | subs_box_inf s : ▢ s ⊑ s.

  Global Instance bsp_subsumption : Subsumption := term_subsumption.

  Lemma bsp_subs_eq s t : s ≡ t -> s ⊑ t.
  Proof. apply subs_eq. Qed.
  Lemma bsp_subs_exchange a b c d : (a ∥ b) ⋅ (c ∥ d) ⊑ (a ⋅ c) ∥ (b ⋅ d).
  Proof. apply subs_exchange. Qed.
  Lemma bsp_subs_box_inf s : ▢ s ⊑ s.
  Proof. apply subs_box_inf. Qed.
  Global Instance bsp_subs_seq : Proper (subsume ==> subsume ==> subsume) prod.
  Proof. repeat intro;eapply subs_seq;assumption. Qed.
  Global Instance bsp_subs_par : Proper (subsume ==> subsume ==> subsume) par.
  Proof. repeat intro;eapply subs_par;assumption. Qed.
  Global Instance bsp_subs_box : Proper (subsume ==> subsume) box.
  Proof. repeat intro;eapply subs_box;assumption. Qed.
  
  Hint Resolve bsp_subs_eq bsp_subs_exchange bsp_subs_box_inf.

  Lemma bsp_subsumption_ind :
    forall P : bsp_terms -> bsp_terms -> Prop,
      (forall s t : bsp_terms, s ≡ t -> P s t) ->
      (forall s t u : bsp_terms, s ⊑ t -> P s t -> t ⊑ u -> P t u -> P s u) ->
      (forall s t s' t' : bsp_terms,
          s ⊑ t -> P s t -> s' ⊑ t' -> P s' t' -> P (s ⋅ s') (t ⋅ t')) ->
      (forall s t s' t' : bsp_terms,
          s ⊑ t -> P s t -> s' ⊑ t' -> P s' t' -> P (s ∥ s') (t ∥ t')) ->
      (forall s t : bsp_terms, s ⊑ t -> P s t -> P (▢ s) (▢ t)) ->
      (forall a b c d : bsp_terms, P ((a ∥ b) ⋅ (c ∥ d)) (a ⋅ c ∥ b ⋅ d)) ->
      (forall s : bsp_terms, P (▢ s) s) ->
      forall s t : bsp_terms, s ⊑ t -> P s t.
  Proof. apply term_subsumption_ind. Qed.

  Global Instance bsp_subsumption_preorder : PreOrder subsume.
  Proof.
    split.
    - intro s;auto.
    - intros s t u h1 h2;eapply subs_trans;eauto.
  Qed.

  
End b.
Arguments bsp_terms : clear implicits.
Hint Constructors bsp_eq.
Hint Rewrite @bsp_size_un @bsp_size_var @bsp_prod_prod @bsp_size_prod @bsp_par_par @bsp_size_par @bsp_box_box @bsp_size_box: simpl_typeclasses.
Hint Resolve bsp_subs_eq bsp_subs_exchange bsp_subs_box.

