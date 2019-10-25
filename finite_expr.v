Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools algebra Bool bindings bsp_terms relations.
  
Section e.
  Context {X : Set}.

  Inductive bbsr_terms {X : Set} : Set :=
    | bbsr_seq : bbsr_terms -> bbsr_terms -> bbsr_terms
    | bbsr_par : bbsr_terms -> bbsr_terms -> bbsr_terms
    | bbsr_plus : bbsr_terms -> bbsr_terms -> bbsr_terms
    | bbsr_var : X -> bbsr_terms
    | bbsr_box : bbsr_terms -> bbsr_terms
    | bbsr_unit : bbsr_terms
    | bbsr_zero : bbsr_terms.

  Global Instance bbsr_seq_prod : Product (@bbsr_terms X) := bbsr_seq.

  Global Instance bbsr_par_prod : ParProduct (@bbsr_terms X) := bbsr_par.

  Global Instance bbsr_plus_Join : Join (@bbsr_terms X) := bbsr_plus.

  Global Instance bbsr_unit_unit : Un (@bbsr_terms X) := bbsr_unit.

  Global Instance bbsr_zero_zero : Zero (@bbsr_terms X) := bbsr_zero.

  Global Instance bbsr_box_Box : Box (@bbsr_terms X) := bbsr_box.

  Global Instance bbsr_size : Size (@bbsr_terms X) :=
    fix bbsr_size s :=
      match s with
      | bbsr_par s1 s2 | bbsr_seq s1 s2 | bbsr_plus s1 s2 => bbsr_size s1 + bbsr_size s2
      | bbsr_box s => bbsr_size s
      | bbsr_unit | bbsr_zero => 0
      | bbsr_var _ => 1
      end.

  Remark bbsr_unit_un : bbsr_unit = @un bbsr_terms _.
  Proof. reflexivity. Qed.
  Remark bbsr_size_un : ⎢𝟭⎥ = 0.
  Proof. reflexivity. Qed.
  Remark bbsr_size_zero : ⎢𝟬⎥ = 0.
  Proof. reflexivity. Qed.
  Remark bbsr_size_var x : ⎢bbsr_var x⎥ = 1.
  Proof. reflexivity. Qed.
  Remark bbsr_box_box s : bbsr_box s = (@box bbsr_terms _ s).
  Proof. reflexivity. Qed.
  Remark bbsr_size_box s : ⎢▢ s⎥ = ⎢s⎥.
  Proof. reflexivity. Qed.
  Remark bbsr_prod_prod s t : bbsr_seq s t = (@prod bbsr_terms _ s t).
  Proof. reflexivity. Qed.
  Remark bbsr_size_prod s t : ⎢s⋅t⎥ = ⎢s⎥+⎢t⎥.
  Proof. reflexivity. Qed.
  Remark bbsr_par_par s t : bbsr_par s t = (@par bbsr_terms _ s t).
  Proof. reflexivity. Qed.
  Remark bbsr_size_par s t : ⎢s∥t⎥ = ⎢s⎥+⎢t⎥.
  Proof. reflexivity. Qed.
  Remark bbsr_plus_join s t : bbsr_plus s t = (@join bbsr_terms _ s t).
  Proof. reflexivity. Qed.
  Remark bbsr_size_join s t : ⎢s∪t⎥ = ⎢s⎥+⎢t⎥.
  Proof. reflexivity. Qed.
  
  Hint Rewrite bbsr_unit_un bbsr_size_zero bbsr_size_un bbsr_size_var bbsr_prod_prod bbsr_size_prod bbsr_par_par bbsr_size_par bbsr_box_box bbsr_size_box
       bbsr_plus_join bbsr_size_join
    : simpl_typeclasses.
  
  Reserved Notation " A ⊢ s ⩵ t " (at level 80).
  
  Inductive bbsr_eq (Ax : relation bbsr_terms) : relation bbsr_terms :=
  | bbsr_eq_refl s : Ax ⊢ s ⩵ s
  | bbsr_eq_sym s t : Ax ⊢ s ⩵ t -> Ax ⊢ t ⩵ s
  | bbsr_eq_trans s t u : Ax ⊢ s ⩵ t -> Ax ⊢ t ⩵ u -> Ax ⊢ s ⩵ u
  | bbsr_eq_seq s t s' t' : Ax ⊢ s ⩵ t -> Ax ⊢ s' ⩵ t' -> Ax ⊢ s ⋅ s' ⩵ t ⋅ t'
  | bbsr_eq_par s t s' t' : Ax ⊢ s ⩵ t -> Ax ⊢ s' ⩵ t' -> Ax ⊢ s ∥ s' ⩵ t ∥ t'
  | bbsr_eq_plus s t s' t' : Ax ⊢ s ⩵ t -> Ax ⊢ s' ⩵ t' -> Ax ⊢ s ∪ s' ⩵ t ∪ t'
  | bbsr_eq_box s t : Ax ⊢ s ⩵ t -> Ax ⊢ ▢ s ⩵ ▢ t
  | bbsr_ax s t : Ax s t -> Ax ⊢ s ⩵ t
  where " A ⊢ s ⩵ t " := (bbsr_eq A s t).
  Hint Constructors bbsr_eq.

  Notation " A ⊢ s ≦ t " := (leqA (bbsr_eq A) s t) (at level 80).
  
  Global Instance Ax_equiv Ax : subrelation Ax (bbsr_eq Ax).
  Proof. intro;intros;auto. Qed.

  Global Instance bbsr_eq_equivalence Ax : Equivalence (bbsr_eq Ax).
  Proof. split;intro;intros;eauto. Qed.

  Global Instance bbsr_seq_proper Ax :
    Proper ((bbsr_eq Ax)==>(bbsr_eq Ax)==>(bbsr_eq Ax)) prod.
  Proof. intros ? ? ? ? ? ?;eauto. Qed.

  Global Instance bbsr_par_proper Ax :
    Proper ((bbsr_eq Ax)==>(bbsr_eq Ax)==>(bbsr_eq Ax)) par.
  Proof. intros ? ? ? ? ? ?;eauto. Qed.

  Global Instance bbsr_plus_proper Ax :
    Proper ((bbsr_eq Ax)==>(bbsr_eq Ax)==>(bbsr_eq Ax)) join.
  Proof. intros ? ? ? ? ? ?;eauto. Qed.

  Global Instance bbsr_box_proper Ax :
    Proper ((bbsr_eq Ax)==>(bbsr_eq Ax)) box.
  Proof. intros ? ? ?;eauto. Qed.

  Global Instance subrelation_Ax_proper : Proper (subrelation ==> subrelation) bbsr_eq.
  Proof. intros A B I e f E;induction E;eauto. Qed.

  Reserved Notation " s =0 t " (at level 80).
  Reserved Notation " s =1 t " (at level 80).
  Reserved Notation " s =2 t " (at level 80).
  
  Inductive bisemiring : relation bbsr_terms :=
  | bbsr_eq_seq_ass s t u : s ⋅ (t ⋅ u) =0 (s ⋅ t) ⋅ u
  | bbsr_eq_par_ass s t u : s ∥ (t ∥ u) =0 (s ∥ t) ∥ u
  | bbsr_eq_plus_ass s t u : s ∪ (t ∪ u) =0 (s ∪ t) ∪ u
  | bbsr_eq_par_comm s t : s ∥ t =0 t ∥ s
  | bbsr_eq_plus_comm s t : s ∪ t =0 t ∪ s
  | bbsr_eq_plus_idem s : s ∪ s =0 s
  | bbsr_eq_seq_left_unit s : 𝟭 ⋅ s =0 s
  | bbsr_eq_seq_right_unit s : s ⋅ 𝟭 =0 s
  | bbsr_eq_par_unit s : 𝟭 ∥ s =0 s
  | bbsr_eq_plus_unit s : 𝟬 ∪ s =0 s
  | bbsr_eq_seq_left_absorbing s : 𝟬 ⋅ s =0 𝟬
  | bbsr_eq_seq_right_absorbing s : s ⋅ 𝟬 =0 𝟬
  | bbsr_eq_par_zero s : 𝟬 ∥ s =0 𝟬
  | bbsr_eq_left_distr s t u : s ⋅ (t ∪ u) =0 (s⋅t)∪(s⋅u)
  | bbsr_eq_right_distr s t u : (s∪t)⋅u =0 (s⋅u)∪(t⋅u)
  | bbsr_eq_par_distr s t u : s ∥ (t ∪ u) =0 (s∥t)∪(s∥u)
  where " s =0 t " := (bisemiring s t).
  
  Inductive box_alg : relation bbsr_terms :=
  | bbsr_eq_box_box s : ▢ (▢ s) =1 ▢ s
  | bbsr_eq_box_unit : ▢ 𝟭 =1 𝟭
  | bbsr_eq_box_zero : ▢ 𝟬 =1 𝟬
  | bbsr_eq_box_plus a b : ▢ (a∪b) =1 (▢ a) ∪ (▢ b)
  where " s =1 t " := (box_alg s t).

  Inductive exchange : relation bbsr_terms :=
  | bbsr_eq_exchange a b c d : (a∥b)⋅(c∥d) ∪ (a⋅c)∥(b⋅d) =2 (a⋅c)∥(b⋅d)
  | bbsr_eq_box_inf a : ▢ a ∪ a =2 a
  where " s =2 t " := (exchange s t).

  Definition BSR : relation bbsr_terms := bisemiring ∪ box_alg.
  Definition BCSR : relation bbsr_terms := BSR ∪ exchange.

  Hint Constructors bisemiring box_alg exchange.

  Global Instance bisemiring_BSR : subrelation bisemiring BSR.
  Proof. apply join_subrel_left. Qed.
 
  Global Instance bisemiring_BCSR : subrelation bisemiring BCSR.
  Proof. unfold BCSR;rewrite <- join_subrel_left;apply join_subrel_left. Qed.
 
  Global Instance BSR_BCSR : subrelation BSR BCSR.
  Proof. apply join_subrel_left. Qed.

  Global Instance box_alg_BSR : subrelation box_alg BSR.
  Proof. apply join_subrel_right. Qed.

  Global Instance box_alg_BCSR : subrelation box_alg BCSR.
  Proof. unfold BCSR;rewrite <- join_subrel_left;apply join_subrel_right. Qed.

  Global Instance exchange_BCSR : subrelation exchange BCSR.
  Proof. apply join_subrel_right. Qed.

  Global Instance bisemiring_bimonoid :
    BiMonoid bbsr_terms (bbsr_eq bisemiring) prod par un.
  Proof. repeat split;repeat intro;eauto. Qed.

  Ltac weak_left := (eapply subrelation_Ax_proper;[apply join_subrel_left|]).
  Ltac weak_right := (eapply subrelation_Ax_proper;[apply join_subrel_right|]).
  
  Global Instance bisemiring_bisemiring :
    BiSemiRing bbsr_terms (bbsr_eq bisemiring) prod par join un zero.
  Proof.
    split.
    - apply bisemiring_bimonoid.
    - split.
      + apply bbsr_plus_proper.
      + intros x y z;eauto.
      + split.
        * intro x;eauto.
        * intro x;eauto.
    - intros x y;eauto.
    - split;intro x;eauto.
    - split;intro x;eauto.
    - intros x y z;eauto.
    - intros x y z;eauto.
    - intros x y z;eauto.
  Qed.

  Global Instance bisemiring_idempotent : @Idempotent _ (bbsr_eq bisemiring) join.
  Proof. intro a;auto. Qed.

  Global Instance bsr_bimonoid :
    BiMonoid bbsr_terms (bbsr_eq BSR) prod par un.
  Proof.
    repeat split;repeat intro; (now apply bbsr_ax;left;auto) || eauto.
    weak_left;eauto.
  Qed.
  Global Instance bsr_bisemiring :
    BiSemiRing bbsr_terms (bbsr_eq BSR) prod par join un zero.
  Proof. repeat split;repeat intro; try tauto || (now repeat weak_left;eauto) || eauto. Qed.

  Global Instance bsr_idempotent : @Idempotent _ (bbsr_eq BSR) join.
  Proof. intro a;weak_left;auto. Qed.


  Section leqA.
    Instance bbsr_semilat : Semilattice bbsr_terms (bbsr_eq BSR) join
      := semi_lat.
    
    Instance bbsr_semiring : SemiRing bbsr_terms (bbsr_eq BSR) prod join un zero
      := bisemiring_is_semiring.

    Global Instance BSR_preOrder : PreOrder (leqA(bbsr_eq BSR))
      := preA.

    Global Instance BSR_partialOrder : PartialOrder (bbsr_eq BSR) (leqA(bbsr_eq BSR))
      := partialA.
    
    Global Instance prod_proper_inf :
      Proper (leqA (bbsr_eq BSR) ==> leqA (bbsr_eq BSR) ==> leqA (bbsr_eq BSR)) prod:=
      proper_prod_inf.

    Global Instance plus_proper_inf :
      Proper (leqA (bbsr_eq BSR) ==> leqA (bbsr_eq BSR) ==> leqA (bbsr_eq BSR)) join:=
      proper_join_inf.

    Global Instance box_proper_inf :
      Proper (leqA (bbsr_eq BSR)==> leqA (bbsr_eq BSR)) bbsr_box.
    Proof. intros e f E;unfold leqA in *;rewrite E at 1; weak_right;rsimpl;auto. Qed.

    Lemma BSR_join_left a b : BSR ⊢ a ≦ a ∪ b.
    Proof. apply inf_cup_left. Qed.

    Lemma BSR_join_right a b : BSR ⊢ b ≦ a ∪ b.
    Proof. apply inf_cup_right. Qed.

    Lemma BSR_join_inf a b c : BSR ⊢ a ≦ c -> BSR ⊢ b ≦ c -> BSR ⊢ a ∪ b ≦ c.
    Proof. apply inf_join_inf. Qed.

    Lemma BSR_zero_minimal x : BSR ⊢ zero ≦ x.
    Proof. apply zero_minimal. Qed.

    Lemma Σ_left_distr e L : BSR ⊢ e ⋅ Σ L ⩵ Σ ([e]⋅ L).
    Proof.
      rewrite Σ_distr_l.
      unfold prod at 2,prod_list;simpl.
      rewrite app_nil_r;reflexivity.
    Qed.
    
    Lemma Σ_right_distr e L : BSR ⊢ Σ L ⋅ e ⩵ Σ (L⋅[e]).
    Proof.
      induction L;simpl.
      - apply left_absorbing.
      - rewrite <- IHL,semiring_right_distr;reflexivity.
    Qed.
    
    Definition ℒ' := (list (@bbsr_terms X)).

    Global Instance eqℒ' : SemEquiv ℒ' := (@eqLang _ (bbsr_eq BSR)).
    Global Instance infℒ' : SemSmaller ℒ' := (@infLang _ (bbsr_eq BSR)).
    
    Global Instance Box_list' : Box ℒ' := map box.

    Global Instance ℒ'_BiSemiRing : BiSemiRing ℒ' sequiv prod par join un zero
      := ListBiSemiRing_bisemiring.
    Global Instance ℒ'_Idem : @Idempotent ℒ' sequiv join
      := ListBiSemiRing_idempotent.
    Instance ℒ'_semiring : SemiRing ℒ' sequiv prod join un zero
      := bisemiring_is_semiring.

    Global Instance Σ_proper_inf : Proper (ssmaller ==> leqA (bbsr_eq BSR)) Σ.
    Proof.
      intros l m I;induction l.
      - apply zero_minimal.
      - simpl;apply inf_join_inf.
        + destruct (I a) as (b&Ib&Eb).
          * now left.
          * rewrite <- Eb.
            apply Σ_bigger,Ib.
        + apply IHl;intros b Ib;apply I;now right.
    Qed.
    
    Global Instance Σ_proper : Proper (sequiv ==> (bbsr_eq BSR)) Σ.
    Proof. intros l m E;apply antisymmetry;apply Σ_proper_inf,E. Qed.
    
    Lemma Σ_prod l m : BSR ⊢ Σ l ⋅ Σ m ⩵ Σ (l⋅m).
    Proof.
      induction l;simpl.
      - apply left_absorbing.
      - rewrite semiring_right_distr,IHl;simpl.
        rewrite Σ_left_distr,Σ_app.
        replace (@app bbsr_terms) with (@join (list (@bbsr_terms X)) _) by reflexivity.
        rewrite <- semiring_right_distr.
        reflexivity.
    Qed.
    
    Instance bbsr_semiring_par : SemiRing bbsr_terms (bbsr_eq BSR) par join un zero
      := bisemiring_is_semiring_par.
    
    Global Instance par_proper_inf :
      Proper (leqA (bbsr_eq BSR) ==> leqA (bbsr_eq BSR) ==> leqA (bbsr_eq BSR)) par:=
      proper_prod_inf.
    
    Lemma Σ_par_distr e L : BSR ⊢ e ∥ Σ L ⩵ Σ ([e] ∥ L).
    Proof.
      induction L;simpl.
      - apply right_absorbing.
      - rewrite <- IHL,bisemiring_par_distr;reflexivity.
    Qed.
    
    Instance ℒ'_semiring_par : SemiRing ℒ' sequiv par join un zero
      := bisemiring_is_semiring_par.

    Lemma Σ_par l m : BSR ⊢ Σ l ∥ Σ m ⩵ Σ (l∥m).
    Proof.
      induction l;simpl.
      - apply left_absorbing.
      - rewrite semiring_right_distr,IHl;simpl.
        rewrite Σ_par_distr,Σ_app.
        replace (@app bbsr_terms) with (@join (list (@bbsr_terms X)) _) by reflexivity.
        rewrite <- semiring_right_distr.
        reflexivity.
    Qed.
    
  End leqA.


  Fixpoint ϵ (e : @bbsr_terms X) : bool :=
    match e with
    | bbsr_seq e f | bbsr_par e f => ϵ e && ϵ f
    | bbsr_plus e f => ϵ e || ϵ f
    | bbsr_box e => ϵ e
    | bbsr_unit => true
    | _ => false
    end.

  
  Lemma ϵ_bigger_unit e : ϵ e = true -> BSR ⊢ 𝟭 ≦ e.
  Proof.
    induction e;simpl.
    - rewrite andb_true_iff;intro E.
      replace bbsr_seq with prod by reflexivity.
      transitivity (𝟭⋅𝟭);[rewrite left_unit;reflexivity|].
      destruct E as (E1&E2);apply IHe1 in E1;apply IHe2 in E2.
      rewrite E1,E2 at 1;reflexivity.
    - rewrite andb_true_iff;intro E.
      replace bbsr_par with par by reflexivity.
      transitivity (𝟭∥𝟭);[rewrite left_unit;reflexivity|].
      destruct E as (E1&E2);apply IHe1 in E1;apply IHe2 in E2.
      rewrite E1,E2 at 1;reflexivity.
    - rewrite orb_true_iff;replace bbsr_plus with join by reflexivity.
      intros [E|E].
      + apply IHe1 in E as ->;apply BSR_join_left.
      + apply IHe2 in E as ->;apply BSR_join_right.
    - discriminate.
    - intros E;transitivity (▢ 𝟭 : bbsr_terms).
      + apply PartialOrder_subrelation;symmetry;weak_right;auto.
      + rewrite (IHe E);reflexivity.
    - reflexivity.
    - discriminate.
  Qed.

  Lemma ϵ_proper_spec Ax :
    Proper (Ax ==> Logic.eq) ϵ -> Proper ((bbsr_eq Ax) ==> Logic.eq) ϵ.
  Proof.
    intros hyp e f E;induction E;simpl;try congruence.
    apply hyp,H.
  Qed.

  Lemma ϵ_proper_bisemiring_axioms : Proper (bisemiring ==> Logic.eq) ϵ.
  Proof.
    intros e f [];simpl;auto with bool.
    - destruct (ϵ s);reflexivity.
    - rewrite andb_true_r;reflexivity.
    - rewrite andb_false_r;reflexivity.
    - destruct (ϵ s);simpl;reflexivity.
    - destruct (ϵ u);simpl;[repeat rewrite andb_true_r
                           |repeat rewrite andb_false_r];reflexivity.
    - destruct (ϵ s);simpl;reflexivity.
  Qed.

  Lemma ϵ_proper_box_alg_axioms : Proper (box_alg ==> Logic.eq) ϵ.
  Proof. intros e f [];simpl;auto with bool. Qed.

  Lemma ϵ_proper_exchange_axioms : Proper (exchange ==> Logic.eq) ϵ.
  Proof.
    intros e f [];simpl;auto with bool.
    - destruct (ϵ a);simpl;auto.
      destruct (ϵ b);simpl;auto.
      destruct (ϵ c);simpl;auto.
      destruct (ϵ d);simpl;auto.
    - destruct (ϵ a);simpl;auto.
  Qed.

  Global Instance ϵ_proper_bisemiring : Proper ((bbsr_eq bisemiring) ==> Logic.eq) ϵ
    := (ϵ_proper_spec ϵ_proper_bisemiring_axioms).
  Global Instance ϵ_proper_BSR : Proper ((bbsr_eq BSR) ==> Logic.eq) ϵ.
  Proof.
    apply ϵ_proper_spec.
    intros ? ? [?|?];[apply ϵ_proper_bisemiring_axioms|apply ϵ_proper_box_alg_axioms];
      assumption.
  Qed.
  
  Global Instance ϵ_proper_BCSR : Proper ((bbsr_eq BCSR) ==> Logic.eq) ϵ.
  Proof.
    apply ϵ_proper_spec.
    intros ? ? [[?|?]|?];[apply ϵ_proper_bisemiring_axioms|apply ϵ_proper_box_alg_axioms
                         |apply ϵ_proper_exchange_axioms];
    assumption.
  Qed.

  Lemma ϵ_spec e : ϵ e = true <-> BSR ⊢ 𝟭 ≦ e.
  Proof.
    split;[apply ϵ_bigger_unit|].
    intros E;apply ϵ_proper_BSR in E as ->;reflexivity.
  Qed.

  (* Definition is_in_lang (u : bsp_terms X) (L : ℒ) := exists v, u ≡ v /\ v ∈ L. *)
  (* Infix " ⋵ " := is_in_lang (at level 80). *)

  (* Instance is_in_lang_proper : Proper (equiv ==> sequiv ==> iff) is_in_lang. *)
  (* Proof. *)
  (*   intros s t E1 L M E2;split. *)
  (*   - intros (s'&E'&I');apply E2 in I' as (t'&I'&E''). *)
  (*     exists t';split;[|assumption]. *)
  (*     rewrite E'',<-E',E1;reflexivity. *)
  (*   - intros (t'&E'&I');apply E2 in I' as (s'&I'&E''). *)
  (*     exists s';split;[|assumption]. *)
  (*     rewrite E'',<-E',E1;reflexivity. *)
  (* Qed. *)
  
  (* Lemma ϵ_lang e : ϵ e = true <-> 𝟭 ⋵ ⟦e⟧. *)
  (* Proof. *)
  (*   rewrite ϵ_spec. *)
  (*   unfold leqA. *)
  (*   rewrite termLang_iso. *)
  (*   split. *)
  (*   - intros E;rewrite E;exists 𝟭;split;[reflexivity|left;reflexivity]. *)
  (*   - intros (x&Ex&Ix);interpret_bbsr. *)
  (*     split. *)
  (*     + intros s I;exists s;split;[right;simpl;assumption|reflexivity]. *)
  (*     + intros s [<-|I]. *)
  (*       * symmetry in Ex;exists x;tauto. *)
  (*       * simpl in I;exists s;split;[assumption|reflexivity]. *)
  (* Qed. *)
  
  
  Fixpoint is_zero (e : @bbsr_terms X) :=
    match e with
    | bbsr_seq e1 e2 | bbsr_par e1 e2 => is_zero e1 || is_zero e2
    | bbsr_plus e1 e2 => is_zero e1 && is_zero e2
    | bbsr_unit | bbsr_var _ => false
    | bbsr_box s => is_zero s
    | bbsr_zero => true
    end.

  Instance is_zero_proper : Proper ((bbsr_eq BCSR) ==> Logic.eq) is_zero.
  Proof.
    intros e f E;induction E;simpl in *;auto.
    - congruence.
    - congruence.
    - congruence.
    - congruence.
    - destruct H as [[[]|[]]|[]];
        try (simpl;apply eq_true_iff_eq;
             repeat rewrite andb_true_iff||rewrite orb_true_iff;tauto).
      simpl;rewrite orb_false_r;reflexivity.
  Qed.

  Proposition is_zero_spec s : is_zero s = true <-> BSR ⊢ s ⩵ 𝟬.
  Proof.
    split;[|intros E;transitivity(is_zero 𝟬);
            [eapply is_zero_proper,subrelation_Ax_proper,E ;apply BSR_BCSR|reflexivity]].
    induction s;simpl in *;try discriminate||rewrite andb_true_iff||rewrite orb_true_iff.
    - intros [I|I];[apply IHs1 in I as ->|apply IHs2 in I as ->];
        replace bbsr_seq with prod by reflexivity.
      + apply left_absorbing.
      + apply right_absorbing.
    - intros [I|I];[apply IHs1 in I as ->|apply IHs2 in I as ->];
        replace bbsr_seq with prod by reflexivity.
      + apply left_absorbing.
      + apply right_absorbing.
    - intros (I1&I2);apply IHs1 in I1 as ->;apply IHs2 in I2 as ->.
      apply left_unit.
    - intros I;rewrite IHs by assumption.
      apply bbsr_ax;right;auto.
    - reflexivity.
  Qed.
  
  Fixpoint width e :=
    if (is_zero e) then 0 else
      match e with
      | bbsr_seq e1 e2 
      | bbsr_plus e1 e2 => width e1 ⊕ width e2
      | bbsr_par e1 e2 => width e1 + width e2
      | bbsr_var _ => 1
      | bbsr_box s => width s
      | bbsr_zero | bbsr_unit => 0
      end.

  Remark zero_width s : is_zero s = true -> width s = 0.
  Proof. destruct s;simpl;try intros ->;discriminate || reflexivity. Qed.

  Ltac case_zero s :=
    let h := fresh "h" in
    case_eq (is_zero s);[intros h;try rewrite (zero_width h)|intros _].
  
  Instance width_proper : Proper ((bbsr_eq BSR) ==> Logic.eq) width.
  Proof.
    intros e f E;induction E;simpl.
    - reflexivity.
    - congruence.
    - congruence.
    - pose proof E1 as E;apply (subrelation_Ax_proper BSR_BCSR) in E;rewrite E at 1;clear E.
      pose proof E2 as E;apply (subrelation_Ax_proper BSR_BCSR) in E;rewrite E at 1;clear E.
      destruct (is_zero t),(is_zero t');simpl;auto.
    - pose proof E1 as E;apply (subrelation_Ax_proper BSR_BCSR) in E;rewrite E at 1;clear E.
      pose proof E2 as E;apply (subrelation_Ax_proper BSR_BCSR) in E;rewrite E at 1;clear E.
      destruct (is_zero t),(is_zero t');simpl;auto.
    - pose proof E1 as E;apply (subrelation_Ax_proper BSR_BCSR) in E;rewrite E at 1;clear E.
      pose proof E2 as E;apply (subrelation_Ax_proper BSR_BCSR) in E;rewrite E at 1;clear E.
      destruct (is_zero t),(is_zero t');simpl;auto.
    - pose proof E as E';apply (subrelation_Ax_proper BSR_BCSR) in E;rewrite E at 1;clear E.
      destruct (is_zero t);simpl;auto.
    - destruct H as [[]|[]];simpl;
        try case_zero s0;try case_zero t0;try case_zero u;try case_zero a;try case_zero b;
          simpl;repeat rewrite Max.max_assoc||rewrite Nat.max_0_r||rewrite Nat.max_0_l;
            try reflexivity||lia.
  Qed.

  Proposition width_positive s : BSR ⊢ s ≦ 𝟭 <-> width s = 0.
  Proof.
    split.
    - unfold leqA;intros E.
      transitivity (width 𝟭);[|reflexivity].
      rewrite E;simpl.
      case_zero s;simpl.
      + reflexivity.
      + lia.
    - induction s;simpl.
      + replace bbsr_seq with prod by reflexivity.
        revert IHs1 IHs2;case_zero s1;[|case_zero s2];simpl;intros.
        * apply is_zero_spec in h as ->;rewrite left_absorbing.
          apply BSR_zero_minimal.
        * apply is_zero_spec in h as ->;rewrite right_absorbing.
          apply BSR_zero_minimal.
        * rewrite IHs1,IHs2.
          -- rewrite left_unit;reflexivity.
          -- lia.
          -- lia.
      + replace bbsr_par with par by reflexivity.
        revert IHs1 IHs2;case_zero s1;[|case_zero s2];simpl;intros.
        * apply is_zero_spec in h as ->;rewrite left_absorbing.
          apply BSR_zero_minimal.
        * apply is_zero_spec in h as ->;rewrite right_absorbing.
          apply BSR_zero_minimal.
        * rewrite IHs1,IHs2.
          -- rewrite left_unit;reflexivity.
          -- lia.
          -- lia.
      + replace bbsr_plus with join by reflexivity.
        revert IHs1 IHs2;case_zero s1;case_zero s2;simpl;intros.
        * apply is_zero_spec in h as ->;apply is_zero_spec in h0 as ->.
          rewrite left_unit;apply BSR_zero_minimal.
        * apply is_zero_spec in h as ->.
          rewrite left_unit;apply IHs2,H.
        * apply is_zero_spec in h as ->.
          rewrite right_unit;apply IHs1.
          lia.
        * transitivity (𝟭∪𝟭).
          -- apply plus_proper_inf;[apply IHs1|apply IHs2];lia.
          -- rewrite bsr_idempotent;reflexivity.
      + discriminate.
      + replace bbsr_box with (@box bbsr_terms _) by reflexivity.
        case_zero s.
        * apply is_zero_spec in h as ->.
          intros _.
          transitivity 𝟬;[|apply zero_minimal].
          apply PartialOrder_subrelation,bbsr_ax;right;auto.
        * intro h;apply IHs in h;clear IHs.
          transitivity (▢ 𝟭:bbsr_terms).
          -- apply box_proper_inf,h.
          -- apply PartialOrder_subrelation,bbsr_ax;right;auto.
      + intros _;reflexivity.
      + intros _;apply zero_minimal.
  Qed.
 
  Inductive Δ : bbsr_terms -> relation bbsr_terms :=
  | Δ_unit_l e : Δ e 𝟭 e
  | Δ_unit_r e : Δ e e 𝟭
  | Δ_sum_l e1 e2 f g : Δ e1 f g -> Δ (e1∪e2) f g
  | Δ_sum_r e1 e2 f g : Δ e2 f g -> Δ (e1∪e2) f g
  | Δ_seq_l e1 e2 f g : Δ e1 f g -> ϵ e2 = true -> Δ (e1⋅e2) f g
  | Δ_seq_r e1 e2 f g : Δ e2 f g -> ϵ e1 = true -> Δ (e1⋅e2) f g
  | Δ_par e1 e2 f1 g1 f2 g2 : Δ e1 f1 g1 -> Δ e2 f2 g2 -> Δ (e1∥e2) (f1∥f2) (g1∥g2).
  Hint Constructors Δ.
  
  Lemma Δ_fin e : exists L, forall g h, Δ e g h <-> (g,h) ∈ L.
  Proof.
    induction e.
    - destruct IHe1 as (L1&h1),IHe2 as (L2&h2).
      case_eq (ϵ e1);case_eq (ϵ e2);intros E2 E1.
      + exists ((e1⋅e2,𝟭)::(𝟭,e1⋅e2)::L1++L2).
        intros g h;simpl;rewrite in_app_iff.
        rewrite <- h1,<-h2;split.
        * intros E;inversion E;subst;auto.
        * intros [E|[E|[E|E]]].
          -- inversion E;subst;auto.
          -- inversion E;subst;auto.
          -- rsimpl;auto.
          -- rsimpl;auto.
      + exists ((e1⋅e2,𝟭)::(𝟭,e1⋅e2)::L2).
        intros g h;simpl.
        rewrite <-h2;split.
        * intros E;inversion E;subst;auto.
          rewrite H4 in E2;discriminate.
        * intros [E|[E|E]].
          -- inversion E;subst;auto.
          -- inversion E;subst;auto.
          -- rsimpl;auto.
      + exists ((e1⋅e2,𝟭)::(𝟭,e1⋅e2)::L1).
        intros g h;simpl.
        rewrite <-h1;split.
        * intros E;inversion E;subst;auto.
          rewrite H4 in E1;discriminate.
        * intros [E|[E|E]].
          -- inversion E;subst;auto.
          -- inversion E;subst;auto.
          -- rsimpl;auto.
      + exists ((e1⋅e2,𝟭)::(𝟭,e1⋅e2)::[]).
        intros g h;simpl;split.
        * intros E;inversion E;subst;auto.
          -- rewrite H4 in E2;discriminate.
          -- rewrite H4 in E1;discriminate.
        * intros [E|[E|E]];inversion E;subst;auto.
    - destruct IHe1 as (L1&h1),IHe2 as (L2&h2).
      exists ((e1∥e2,𝟭)::(𝟭,e1∥e2)::(lift_prod  (fun x y => (fst x∥fst y,snd x∥snd y)) L1 L2)).
      intros g h;simpl.
      rewrite lift_prod_spec;split.
      + intros E;inversion E;subst;auto.
        right;right.
        apply h1 in H1.
        apply h2 in H4.
        eexists;eexists;split;[|split];try eassumption.
        reflexivity.
      + intros [E|[E|((a,b)&(c,d)&I1&I2&E)]];inversion E;subst;auto.
        apply h1 in I1;apply h2 in I2;rsimpl;auto.
    - destruct IHe1 as (L1&h1),IHe2 as (L2&h2).
      exists ((e1∪e2,𝟭)::(𝟭,e1∪e2)::L1++L2).
      intros g h;simpl;rewrite in_app_iff.
      rewrite <- h1,<-h2;split.
      + intros E;inversion E;subst;auto.
      + intros [E|[E|[E|E]]];inversion E;subst;rsimpl;auto.
    - exists ((bbsr_var x,𝟭)::(𝟭,bbsr_var x)::[]).
      intros g h;split.
      + intro E;inversion E;subst;simpl;auto.
      + intros [E|[E|E]];inversion E;subst;simpl;auto.
    - exists ((▢ e,𝟭)::(𝟭,▢ e)::[]).
      intros g h;split.
      + intro E;inversion E;subst;simpl;auto.
      + intros [E|[E|E]];inversion E;subst;simpl;auto.
    - exists [(𝟭,𝟭)].
      intros g h;split.
      + intro E;inversion E;subst;simpl;auto.
      + intros [E|E];inversion E;subst;simpl;auto.
    - exists [(𝟬,𝟭);(𝟭,𝟬)].
      intros g h;split.
      + intro E;inversion E;subst;simpl;auto.
      + intros [E|[E|E]];inversion E;subst;simpl;auto.
  Qed.
      
  Lemma Δ_inf s t e : Δ e s t -> BSR ⊢ s ∥ t ≦ e.
  Proof.
    intros E;induction E.
    - rewrite left_unit;reflexivity.
    - rewrite right_unit;reflexivity.
    - rewrite <- BSR_join_left;assumption.
    - rewrite <- BSR_join_right;assumption.
    - apply ϵ_spec in H.
      rewrite IHE.
      etransitivity;[|apply prod_proper_inf;[reflexivity|apply H]].
      rewrite right_unit.
      reflexivity.
    - apply ϵ_spec in H.
      rewrite IHE.
      etransitivity;[|apply prod_proper_inf;[apply H|reflexivity]].
      rewrite left_unit.
      reflexivity.
    - etransitivity;[|apply par_proper_inf;eassumption].
      apply PartialOrder_subrelation;clear.
      repeat rewrite (mon_assoc _);apply bbsr_eq_par;[|reflexivity].
      repeat rewrite <-(mon_assoc _);apply bbsr_eq_par;[reflexivity|].
      apply bimon_comm.
  Qed.

  (* Lemma Δ_lang s t e : s ∥ t ⋵ ⟦e⟧ -> exists e1 e2, Δ e e1 e2 /\ s ⋵ ⟦e1⟧ /\ t ⋵ ⟦e2⟧. *)
  (* Proof. *)
  (*   revert s t;induction e;intros s t (u&E&I);interpret_bbsr. *)
  (*   - rsimpl in I;interpret_bbsr;unfold prod,prod_list in I. *)
  (*     apply lift_prod_spec in I as (u1&u2&I1&I2&->). *)
  (*     cut (s ≡ 𝟭 \/ t ≡ 𝟭 \/ u1 ≡ 𝟭 \/ u2 ≡ 𝟭);[|admit]. *)
  (*     intros h;repeat destruct h as [h|h]. *)
  (*     + rewrite h,left_unit in E. *)
  (*       exists 𝟭,(e1⋅e2);repeat split;auto. *)
  (*       * exists 𝟭;split;[assumption|left;reflexivity]. *)
  (*       * exists (u1⋅u2);split;[assumption|]. *)
  (*         apply lift_prod_spec;exists u1,u2;tauto. *)
  (*     + rewrite h,right_unit in E. *)
  (*       exists (e1⋅e2),𝟭;repeat split;auto. *)
  (*       * exists (u1⋅u2);split;[assumption|]. *)
  (*         apply lift_prod_spec;exists u1,u2;tauto. *)
  (*       * exists 𝟭;split;[assumption|left;reflexivity]. *)
  (*     + rewrite h,left_unit in E. *)
  (*       destruct (IHe2 s t) as (l&r&ih&ih1&ih2). *)
  (*       * exists u2;tauto. *)
  (*       * exists l,r;split;[|tauto]. *)
  (*         apply Δ_seq_r;[assumption|]. *)
  (*         apply ϵ_lang. *)
  (*         exists u1;split;auto. *)
  (*     + rewrite h,right_unit in E. *)
  (*       destruct (IHe1 s t) as (l&r&ih&ih1&ih2). *)
  (*       * exists u1;tauto. *)
  (*       * exists l,r;split;[|tauto]. *)
  (*         apply Δ_seq_l;[assumption|]. *)
  (*         apply ϵ_lang. *)
  (*         exists u2;split;auto. *)
  (*   - rsimpl in I;interpret_bbsr;unfold par,par_list in I. *)
  (*     apply lift_prod_spec in I as (u1&u2&I1&I2&->). *)
  (*     cut (exists s1 s2 s3 s4, s ≡ s1 ∥ s2 /\ t ≡ s3 ∥ s4 /\ u1 ≡ s1 ∥ s3 /\ u2 ≡ s2 ∥ s4); *)
  (*       [|admit]. *)
  (*     intros (s1&s2&t1&t2&Es&Et&Eu1&Eu2). *)
  (*     destruct (IHe1 s1 t1) as (l1&r1&h1&Is1&It1);[exists u1;split;auto|]. *)
  (*     destruct (IHe2 s2 t2) as (l2&r2&h2&Is2&It2);[exists u2;split;auto|]. *)
  (*     exists (l1∥l2),(r1∥r2);repeat split;auto. *)
  (*     + interpret_bbsr. *)
  (*       rewrite Es. *)
  (*       destruct Is1 as (s'1&Es1&Is'1). *)
  (*       destruct Is2 as (s'2&Es2&Is'2). *)
  (*       exists (s'1∥s'2);split;auto. *)
  (*       apply lift_prod_spec;exists s'1,s'2;try tauto. *)
  (*     + interpret_bbsr. *)
  (*       rewrite Et. *)
  (*       destruct It1 as (t'1&Et1&It'1). *)
  (*       destruct It2 as (t'2&Et2&It'2). *)
  (*       exists (t'1∥t'2);split;auto. *)
  (*       apply lift_prod_spec;exists t'1,t'2;try tauto. *)
  (*   - apply in_app_iff in I as [I|I]. *)
  (*     + destruct (IHe1 s t) as (l&r&D&Is&It);[exists u;tauto|]. *)
  (*       exists l,r;repeat split;auto. *)
  (*     + destruct (IHe2 s t) as (l&r&D&Is&It);[exists u;tauto|]. *)
  (*       exists l,r;repeat split;auto. *)
  (*   - cut (s ≡ 𝟭 \/ t ≡ 𝟭);[|admit]. *)
  (*     intros h;repeat destruct h as [h|h]. *)
  (*     + destruct I as [<-|[]]. *)
  (*       rewrite h,left_unit in E. *)
  (*       exists 𝟭,(bbsr_var x);repeat split;auto. *)
  (*       * exists 𝟭;split;auto. *)
  (*         left;reflexivity. *)
  (*       * exists (bsp_var x);split;auto. *)
  (*         left;reflexivity. *)
  (*     + destruct I as [<-|[]]. *)
  (*       rewrite h,right_unit in E. *)
  (*       exists (bbsr_var x),𝟭;repeat split;auto. *)
  (*       * exists (bsp_var x);split;auto. *)
  (*         left;reflexivity. *)
  (*       * exists 𝟭;split;auto. *)
  (*         left;reflexivity. *)
  (*   - rsimpl in I;interpret_bbsr;unfold box,Box_list in I. *)
  (*     apply in_map_iff in I as (v&<-&Iv). *)
  (*     cut (s ≡ 𝟭 \/ t ≡ 𝟭);[|admit]. *)
  (*     intros h;repeat destruct h as [h|h]. *)
  (*     + rewrite h,left_unit in E. *)
  (*       exists 𝟭,(▢ e);repeat split;auto. *)
  (*       * exists 𝟭;split;auto. *)
  (*         left;reflexivity. *)
  (*       * exists (▢ v);split;auto. *)
  (*         apply in_map_iff;exists v;tauto. *)
  (*     + rewrite h,right_unit in E. *)
  (*       exists (▢ e),𝟭;repeat split;auto. *)
  (*       * exists (▢ v);split;auto. *)
  (*         apply in_map_iff;exists v;tauto. *)
  (*       * exists 𝟭;split;auto. *)
  (*         left;reflexivity. *)
  (*   - destruct I as [<-|[]]. *)
  (*     cut (s ≡ 𝟭 /\ t ≡ 𝟭);[|admit]. *)
  (*     intros (h1&h2). *)
  (*     exists 𝟭,𝟭;repeat split;auto;exists 𝟭;split;auto;left;reflexivity. *)
  (*   - exfalso;apply I. *)
  (* Admitted. *)
      
  (* Global Instance bcsr_bimonoid : *)
  (*   BiMonoid bbsr_terms (bbsr_eq BCSR) prod par un. *)
  (* Proof. repeat split;repeat intro; try tauto || (now repeat weak_left;eauto) || eauto. Qed. *)
  
  (* Global Instance bcsr_bisemiring : *)
  (*   BiSemiRing bbsr_terms (bbsr_eq BCSR) prod par join un zero. *)
  (* Proof. repeat split;repeat intro; try tauto || (now repeat weak_left;eauto) || eauto. Qed. *)

  
  Global Instance bcsr_bimonoid :
    BiMonoid bbsr_terms (bbsr_eq BCSR) prod par un.
  Proof.
    repeat split;repeat intro; (now apply bbsr_ax;left;left;auto) || eauto.
    weak_left;weak_left;eauto.
  Qed.
  Global Instance bcsr_bisemiring :
    BiSemiRing bbsr_terms (bbsr_eq BCSR) prod par join un zero.
  Proof. repeat split;repeat intro; try tauto || (now repeat weak_left;eauto) || eauto. Qed.

  Global Instance bcsr_idempotent : @Idempotent _ (bbsr_eq BCSR) join.
  Proof. intro a;weak_left;weak_left;auto. Qed.

  Section leqA'.
    Instance bcsr_semilat : Semilattice bbsr_terms (bbsr_eq BCSR) join
      := semi_lat.
    
    Instance bcsr_semiring : SemiRing bbsr_terms (bbsr_eq BCSR) prod join un zero
      := bisemiring_is_semiring.

    Global Instance BCSR_preOrder : PreOrder (leqA(bbsr_eq BCSR))
      := preA.

    Global Instance BCSR_partialOrder : PartialOrder (bbsr_eq BCSR) (leqA(bbsr_eq BCSR))
      := partialA.
    
    Global Instance BCSR_prod_proper_inf :
      Proper (leqA (bbsr_eq BCSR) ==> leqA (bbsr_eq BCSR) ==> leqA (bbsr_eq BCSR)) prod:=
      proper_prod_inf.

    Global Instance BCSR_plus_proper_inf :
      Proper (leqA (bbsr_eq BCSR) ==> leqA (bbsr_eq BCSR) ==> leqA (bbsr_eq BCSR)) join:=
      proper_join_inf.

    Global Instance BCSR_box_proper_inf :
      Proper (leqA (bbsr_eq BCSR)==> leqA (bbsr_eq BCSR)) bbsr_box.
    Proof.
      intros e f E;unfold leqA in *;rewrite E at 1; weak_left;weak_right;rsimpl;auto.
    Qed.

    Global Instance BCSR_BSR_eq : subrelation (bbsr_eq BSR) (bbsr_eq BCSR).
    Proof. apply subrelation_Ax_proper,BSR_BCSR. Qed.
    Global Instance BCSR_BSR_inf : subrelation (leqA (bbsr_eq BSR)) (leqA (bbsr_eq BCSR)).
    Proof. intros e f;unfold leqA;intros <-;reflexivity. Qed.
    
    Lemma BCSR_join_inf a b c : BCSR ⊢ a ≦ c -> BCSR ⊢ b ≦ c -> BCSR ⊢ a ∪ b ≦ c.
    Proof. apply inf_join_inf. Qed.

    Instance bcsr_semiring_par : SemiRing bbsr_terms (bbsr_eq BCSR) par join un zero
      := bisemiring_is_semiring_par.
    
    Global Instance BCSR_par_proper_inf :
      Proper (leqA (bbsr_eq BCSR) ==> leqA (bbsr_eq BCSR) ==> leqA (bbsr_eq BCSR)) par:=
      proper_prod_inf.
   
  End leqA'.

End e.
Notation " A ⊢ s ⩵ t " := (bbsr_eq A s t) (at level 80).
Hint Constructors bbsr_eq.
Hint Constructors bisemiring box_alg exchange.

Notation " A ⊢ s ≦ t " := (leqA (bbsr_eq A) s t) (at level 80).

Ltac weak_left := (eapply subrelation_Ax_proper;[apply join_subrel_left|]).
Ltac weak_right := (eapply subrelation_Ax_proper;[apply join_subrel_right|]).

Hint Rewrite @bbsr_size_zero @bbsr_size_un @bbsr_size_var @bbsr_prod_prod @bbsr_size_prod @bbsr_par_par @bbsr_size_par @bbsr_box_box @bbsr_size_box @bbsr_plus_join @bbsr_size_join
  : simpl_typeclasses.
