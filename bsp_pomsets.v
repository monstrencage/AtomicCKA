Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools algebra Bool relations bsp_terms pomsets.

Section s.
  Context {X : Set}.  
    
  Global Instance sem_bsp : Semantics (bsp_terms X) (Pomset X) :=
    fix I s :=
      match s with
      | bsp_seq s1 s2 => I s1 ⋅ I s2
      | bsp_par s1 s2 => I s1 ∥ I s2
      | bsp_unit => 𝟭
      | bsp_var x => AtomicPomset x
      | bsp_box s => ▢ (I s)
      end.

  Remark interpret_bsp_seq s1 s2 : ⟦s1⋅s2⟧ =  ⟦s1⟧⋅⟦s2⟧.
  Proof. reflexivity. Qed.
  Remark interpret_bsp_par s1 s2 : ⟦s1∥s2⟧ =  ⟦s1⟧∥⟦s2⟧.
  Proof. reflexivity. Qed.
  Remark interpret_bsp_box s : ⟦▢ s⟧ = ▢ ⟦s⟧.
  Proof. reflexivity. Qed.
  Remark interpret_bsp_unit : ⟦𝟭⟧ = 𝟭.
  Proof. reflexivity. Qed.
  Hint Rewrite interpret_bsp_unit interpret_bsp_seq interpret_bsp_par interpret_bsp_box
    : simpl_typeclasses.

  Notation " ⌊| e |⌋ " := ⌊⟦e⟧⌋.
  Notation " ⟨| e |⟩ " := ⟪PomType ⟦e⟧⟫.

  Lemma soundness_bsp_terms s t : s ≡ t -> ⟦s⟧ ≃ ⟦t⟧.
  Proof.
    intros E;induction E;rsimpl.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - rewrite IHE,IHE0;reflexivity.
    - rewrite IHE,IHE0;reflexivity.
    - rewrite IHE;reflexivity.
    - apply mon_assoc.
    - apply mon_assoc.
    - apply bimon_comm.
    - apply left_unit.
    - apply right_unit.
    - apply left_unit.
    - apply Pomset_box_box.
    - apply Pomset_box_unit.
  Qed.

  Global Instance interpret_bsp_proper : Proper (equiv ==> sequiv) interpret.
  Proof. intros x y; apply soundness_bsp_terms. Qed.

  Lemma interpret_bsp_size s : ⎢s⎥ = ⎢⟦s⟧⎥.
  Proof.
    induction s;rsimpl.
    - rewrite IHs1,IHs2.
      destruct ⟦s1⟧,⟦s2⟧;unfold size,sizePomset;simpl.
      rewrite size_node;reflexivity.
    - rewrite IHs1,IHs2.
      destruct ⟦s1⟧,⟦s2⟧;unfold size,sizePomset;simpl.
      rewrite size_node;reflexivity.
    - reflexivity.
    - rewrite IHs;destruct ⟦s⟧;unfold box,boxPomsets,size,sizePomset;simpl.
      reflexivity.
    - reflexivity.
  Qed.

  Global Instance bsp_pomsets_SP_pomsets : forall s, SP_Pomset ⟦s⟧.
  Proof.
    intros s;split;induction s;rsimpl.
    - apply N_free_seq;assumption.
    - apply N_free_par;assumption.
    - apply N_free_atomic.
    - apply N_free_box;assumption.
    - apply N_free_unit.
    - apply WellFormed_seq;assumption.
    - apply WellFormed_par;assumption.
    - apply WellFormed_Atomic.
    - apply WellFormed_box;assumption.
    - apply WellFormed_unit.
    - apply seqOrder_decOrder;assumption.
    - apply sumOrder_decOrder;assumption.
    - apply Oϒ_decOrder.
    - assumption.
    - intros ? ?;left;tauto.
  Qed.

  (** * Sequential decomposition *)
  (** ** pomsets. *)
  Definition get_seq_left {P Q : Pomset X} : list ⌊P⋅Q⌋ -> list ⌊P⌋ :=
    (fun x => inl x : ⟨PomType P ⊎ PomType Q⟩) ¯¹.

  Lemma get_seq_left_spec {P Q : Pomset X} (l : list ⌊P⋅Q⌋) :
    forall e : ⌊P⌋, e ∈ get_seq_left l <-> inl e ∈ l.
  Proof. intro;unfold get_seq_left;rewrite preimage_spec;firstorder subst;auto. Qed.

  Definition get_seq_right {P Q : Pomset X} : list ⌊P⋅Q⌋ -> list ⌊Q⌋ :=
    (fun x => inr x : ⟨PomType P ⊎ PomType Q⟩) ¯¹.

  Lemma get_seq_right_spec {P Q} (l : list ⌊P⋅Q⌋) :
    forall e, e ∈ (get_seq_right l) <-> inr e ∈ l.
  Proof. intro e;unfold get_seq_right;rewrite preimage_spec;firstorder subst;auto. Qed.

  Lemma get_seq_seq_proj P Q (l : list ⌊P ⋅ Q⌋) :
    l ≈ map inl (get_seq_left l) ++ map inr (get_seq_right l).
  Proof.
    intro e.
    rewrite in_app_iff;repeat rewrite in_map_iff.
    setoid_rewrite get_seq_left_spec.
    setoid_rewrite get_seq_right_spec.
    split.
    - destruct e as [e'|e'];intros;[left|right];exists e';tauto.
    - intros [I|I];destruct I as (e'&<-&Ie');assumption.
  Qed.

  Lemma seq_proj_get_seq_l P Q (l : list ⌊P⌋) :
    l ≈ get_seq_left (map (@inl _ ⌊Q⌋) l).
  Proof.
    intro e;rewrite get_seq_left_spec,in_map_iff.
    split.
    - intro Ie;exists e;tauto.
    - intros (e'&E&Ie);inversion E;subst;assumption.
  Qed.

  Lemma seq_proj_get_seq_r P Q (l : list ⌊Q⌋) :
    l ≈ get_seq_right (map (@inr ⌊P⌋ ⌊Q⌋) l).
  Proof.
    intro e;rewrite get_seq_right_spec,in_map_iff.
    split.
    - intro Ie;exists e;tauto.
    - intros (e'&E&Ie);inversion E;subst;assumption.
  Qed.

  Lemma seq_proj_get_seq_l_r P Q (l : list ⌊P⌋) :
    get_seq_right (map (@inl ⌊P⌋ ⌊Q⌋) l) = [].
  Proof.
    case_eq (get_seq_right (map (@inl ⌊P⌋ ⌊Q⌋) l));[reflexivity|].
    intros e L E;exfalso;cut (e ∈ (e::L));[|now left].
    rewrite <- E;intro Ie;apply get_seq_right_spec,in_map_iff in Ie
      as (y&F&_).
    discriminate.
  Qed.
  Lemma seq_proj_get_seq_r_l P Q (l : list ⌊Q⌋) :
    get_seq_left (map (@inr ⌊P⌋ ⌊Q⌋) l) = [].
  Proof.
    case_eq (get_seq_left (map (@inr ⌊P⌋ ⌊Q⌋) l));[reflexivity|].
    intros e L E;exfalso;cut (e ∈ (e::L));[|now left].
    rewrite <- E;intro Ie;apply get_seq_left_spec,in_map_iff in Ie
      as (y&F&_);discriminate.
  Qed.

  (** ** terms. *)
  Definition bsp_get_seq_left {s t : bsp_terms X} (l : list ⌊|bsp_seq s t|⌋) : list ⌊|s|⌋
    := get_seq_left l.
  Definition bsp_get_seq_right {s t : bsp_terms X} (l : list ⌊|bsp_seq s t|⌋) : list ⌊|t|⌋
    := get_seq_right l.
  
  Lemma bsp_get_seq_seq_proj s t (l : list ⌊|s ⋅ t|⌋) :
    l ≈ map inl (bsp_get_seq_left l) ++ map inr (bsp_get_seq_right l).
  Proof. apply get_seq_seq_proj. Qed.

  Lemma bsp_seq_proj_get_seq_l s t (l : list ⌊|s|⌋) :
    l ≈ bsp_get_seq_left (map (@inl _ ⌊|t|⌋) l).
  Proof. apply seq_proj_get_seq_l. Qed.

  Lemma bsp_seq_proj_get_seq_r s t (l : list ⌊|t|⌋) :
    l ≈ bsp_get_seq_right (map (@inr ⌊|s|⌋ ⌊|t|⌋) l).
  Proof. apply seq_proj_get_seq_r. Qed.

  Lemma bsp_seq_proj_get_seq_l_r s t (l : list ⌊|s|⌋) :
    bsp_get_seq_right (map (@inl ⌊|s|⌋ ⌊|t|⌋) l) = [].
  Proof. apply seq_proj_get_seq_l_r. Qed.
  
  Lemma bsp_seq_proj_get_seq_r_l s t (l : list ⌊|t|⌋) :
    bsp_get_seq_left (map (@inr ⌊|s|⌋ ⌊|t|⌋) l) = [].
  Proof. apply seq_proj_get_seq_r_l. Qed.
  
  (** * Parallel decomposition *)
  (** ** pomsets. *)
  Definition get_par_left {P Q : Pomset X} : list ⌊P∥Q⌋ -> list ⌊P⌋ :=
    (fun x => inl x : ⟨PomType P ⊎ PomType Q⟩) ¯¹.

  Lemma get_par_left_spec {P Q : Pomset X} (l : list ⌊P∥Q⌋) :
    forall e : ⌊P⌋, e ∈ get_par_left l <-> inl e ∈ l.
  Proof. intro;unfold get_par_left;rewrite preimage_spec;firstorder subst;auto. Qed.

  Definition get_par_right {P Q : Pomset X} : list ⌊P∥Q⌋ -> list ⌊Q⌋ :=
    (fun x => inr x : ⟨PomType P ⊎ PomType Q⟩) ¯¹.

  Lemma get_par_right_spec {P Q} (l : list ⌊P∥Q⌋) :
    forall e, e ∈ (get_par_right l) <-> inr e ∈ l.
  Proof. intro e;unfold get_par_right;rewrite preimage_spec;firstorder subst;auto. Qed.

  Lemma get_par_par_proj P Q (l : list ⌊P ∥ Q⌋) :
    l ≈ map inl (get_par_left l) ++ map inr (get_par_right l).
  Proof.
    intro e.
    rewrite in_app_iff;repeat rewrite in_map_iff.
    setoid_rewrite get_par_left_spec.
    setoid_rewrite get_par_right_spec.
    split.
    - destruct e as [e'|e'];intros;[left|right];exists e';tauto.
    - intros [I|I];destruct I as (e'&<-&Ie');assumption.
  Qed.

  Lemma par_proj_get_par_l P Q (l : list ⌊P⌋) :
    l ≈ get_par_left (map (@inl _ ⌊Q⌋) l).
  Proof.
    intro e;rewrite get_par_left_spec,in_map_iff.
    split.
    - intro Ie;exists e;tauto.
    - intros (e'&E&Ie);inversion E;subst;assumption.
  Qed.

  Lemma par_proj_get_par_r P Q (l : list ⌊Q⌋) :
    l ≈ get_par_right (map (@inr ⌊P⌋ ⌊Q⌋) l).
  Proof.
    intro e;rewrite get_par_right_spec,in_map_iff.
    split.
    - intro Ie;exists e;tauto.
    - intros (e'&E&Ie);inversion E;subst;assumption.
  Qed.

  Lemma par_proj_get_par_l_r P Q (l : list ⌊P⌋) :
    get_par_right (map (@inl ⌊P⌋ ⌊Q⌋) l) = [].
  Proof.
    case_eq (get_par_right (map (@inl ⌊P⌋ ⌊Q⌋) l));[reflexivity|].
    intros e L E;exfalso;cut (e ∈ (e::L));[|now left].
    rewrite <- E;intro Ie;apply get_par_right_spec,in_map_iff in Ie
      as (y&F&_).
    discriminate.
  Qed.
  Lemma par_proj_get_par_r_l P Q (l : list ⌊Q⌋) :
    get_par_left (map (@inr ⌊P⌋ ⌊Q⌋) l) = [].
  Proof.
    case_eq (get_par_left (map (@inr ⌊P⌋ ⌊Q⌋) l));[reflexivity|].
    intros e L E;exfalso;cut (e ∈ (e::L));[|now left].
    rewrite <- E;intro Ie;apply get_par_left_spec,in_map_iff in Ie
      as (y&F&_);discriminate.
  Qed.

  (** ** terms. *)
  Definition bsp_get_par_left {s t : bsp_terms X} (l : list ⌊|bsp_par s t|⌋) : list ⌊|s|⌋
    := get_par_left l.
  Definition bsp_get_par_right {s t : bsp_terms X} (l : list ⌊|bsp_par s t|⌋) : list ⌊|t|⌋
    := get_par_right l.

  
  Lemma bsp_get_par_par_proj s t (l : list ⌊|s ∥ t|⌋) :
    l ≈ map inl (bsp_get_par_left l) ++ map inr (bsp_get_par_right l).
  Proof. apply get_par_par_proj. Qed.

  Lemma bsp_par_proj_get_par_l s t (l : list ⌊|s|⌋) :
    l ≈ bsp_get_par_left (map (@inl _ ⌊|t|⌋) l).
  Proof. apply par_proj_get_par_l. Qed.

  Lemma bsp_par_proj_get_par_r s t (l : list ⌊|t|⌋) :
    l ≈ bsp_get_par_right (map (@inr ⌊|s|⌋ ⌊|t|⌋) l).
  Proof. apply par_proj_get_par_r. Qed.

  Lemma bsp_par_proj_get_par_l_r s t (l : list ⌊|s|⌋) :
    bsp_get_par_right (map (@inl ⌊|s|⌋ ⌊|t|⌋) l) = [].
  Proof. apply par_proj_get_par_l_r. Qed.
  
  Lemma bsp_par_proj_get_par_r_l s t (l : list ⌊|t|⌋) :
    bsp_get_par_left (map (@inr ⌊|s|⌋ ⌊|t|⌋) l) = [].
  Proof. apply par_proj_get_par_r_l. Qed.
  
  Definition get_box_boxes {s : bsp_terms X} : list ⌊|bsp_box s|⌋ -> list ⌊|s|⌋ := id.

      Global Instance get_seq_left_proper s t : Proper (@equivalent _ ==> @equivalent _)
                                            (@get_seq_left s t).
  Proof. intros l m E e;rewrite get_seq_left_spec,get_seq_left_spec,E;reflexivity. Qed.
  Global Instance get_seq_right_proper s t : Proper (@equivalent _ ==> @equivalent _)
                                             (@get_seq_right s t).
  Proof. intros l m E e;rewrite get_seq_right_spec,get_seq_right_spec,E;reflexivity. Qed.
  Global Instance get_par_left_proper s t : Proper (@equivalent _ ==> @equivalent _)
                                            (@get_par_left s t).
  Proof. intros l m E e;rewrite get_par_left_spec,get_par_left_spec,E;reflexivity. Qed.
  Global Instance get_par_right_proper s t : Proper (@equivalent _ ==> @equivalent _)
                                             (@get_par_right s t).
  Proof. intros l m E e;rewrite get_par_right_spec,get_par_right_spec,E;reflexivity. Qed.
  Global Instance bsp_get_seq_left_proper s t : Proper (@equivalent _ ==> @equivalent _)
                                            (@bsp_get_seq_left s t).
  Proof. apply get_seq_left_proper. Qed.
  Global Instance bsp_get_seq_right_proper s t : Proper (@equivalent _ ==> @equivalent _)
                                             (@bsp_get_seq_right s t).
  Proof. apply get_seq_right_proper. Qed.
  Global Instance bsp_get_par_left_proper s t : Proper (@equivalent _ ==> @equivalent _)
                                            (@bsp_get_par_left s t).
  Proof. apply get_par_left_proper. Qed.
  Global Instance bsp_get_par_right_proper s t : Proper (@equivalent _ ==> @equivalent _)
                                             (@bsp_get_par_right s t).
  Proof. apply get_par_right_proper. Qed.

  Global Instance get_box_boxes_proper s :
    Proper (@equivalent _ ==> @equivalent _) (@get_box_boxes s).
  Proof.
    intros l m;revert l m;unfold get_box_boxes.
    unfold interpret;simpl.
    destruct (sem_bsp s);unfold id;tauto.
  Qed.

  Global Instance get_seq_left_proper_inf s t : Proper (@incl _ ==> @incl _)
                                            (@get_seq_left s t).
  Proof. intros l m E e;rewrite get_seq_left_spec,get_seq_left_spec,E;tauto. Qed.
  Global Instance get_seq_right_proper_inf s t : Proper (@incl _ ==> @incl _)
                                             (@get_seq_right s t).
  Proof. intros l m E e;rewrite get_seq_right_spec,get_seq_right_spec,E;tauto. Qed.
  Global Instance get_par_left_proper_inf s t : Proper (@incl _ ==> @incl _)
                                            (@get_par_left s t).
  Proof. intros l m E e;rewrite get_par_left_spec,get_par_left_spec,E;tauto. Qed.
  Global Instance get_par_right_proper_inf s t : Proper (@incl _ ==> @incl _)
                                             (@get_par_right s t).
  Proof. intros l m E e;rewrite get_par_right_spec,get_par_right_spec,E;tauto. Qed.
  Global Instance bsp_get_seq_left_proper_inf s t : Proper (@incl _ ==> @incl _)
                                            (@bsp_get_seq_left s t).
  Proof. apply get_seq_left_proper_inf. Qed.
  Global Instance bsp_get_seq_right_proper_inf s t : Proper (@incl _ ==> @incl _)
                                             (@bsp_get_seq_right s t).
  Proof. apply get_seq_right_proper_inf. Qed.
  Global Instance bsp_get_par_left_proper_inf s t : Proper (@incl _ ==> @incl _)
                                            (@bsp_get_par_left s t).
  Proof. apply get_par_left_proper_inf. Qed.
  Global Instance bsp_get_par_right_proper_inf s t : Proper (@incl _ ==> @incl _)
                                             (@bsp_get_par_right s t).
  Proof. apply get_par_right_proper_inf. Qed.

  Global Instance get_box_boxes_proper_inf s :
    Proper (@incl _ ==> @incl _) (@get_box_boxes s).
  Proof.
    intros l m;revert l m;unfold get_box_boxes.
    unfold interpret;simpl.
    destruct (sem_bsp s);unfold id;tauto.
  Qed.

  Lemma bsp_get_seq_left_complement s t l :
    ¬ (@bsp_get_seq_left s t l) ≈ (bsp_get_seq_left (¬l)).
  Proof.
    intro e.
    rewrite <- complement_spec.
    setoid_rewrite get_seq_left_spec.
    assert (exists y : ⌊|s⋅t|⌋, y = inl e) as (y & Ey) by (exists (inl e);reflexivity).
    rewrite <- Ey at 2.
    rewrite <- (@complement_spec (PomType ⟦ bsp_seq s t ⟧) y l).
    rewrite Ey;tauto.
  Qed.
  Lemma bsp_get_seq_right_complement s t l :
    ¬ (@bsp_get_seq_right s t l) ≈ (bsp_get_seq_right (¬l)).
  Proof.
    intro e.
    rewrite <- complement_spec.
    setoid_rewrite get_seq_right_spec.
    assert (exists y : ⌊|s⋅t|⌋, y = inr e) as (y & Ey) by (exists (inr e);reflexivity).
    rewrite <- Ey at 2.
    rewrite <- (@complement_spec (PomType ⟦ bsp_seq s t ⟧) y l).
    rewrite Ey;tauto.
  Qed.
  Lemma bsp_get_par_left_complement s t l :
    ¬ (@bsp_get_par_left s t l) ≈ (bsp_get_par_left (¬l)).
  Proof.
    intro e.
    rewrite <- complement_spec.
    setoid_rewrite get_seq_left_spec.
    assert (exists y : ⌊|s∥t|⌋, y = inl e) as (y & Ey) by (exists (inl e);reflexivity).
    rewrite <- Ey at 2.
    rewrite <- (@complement_spec (PomType ⟦ bsp_par s t ⟧) y l).
    rewrite Ey;tauto.
  Qed.
  Lemma bsp_get_par_right_complement s t l :
    ¬ (@bsp_get_par_right s t l) ≈ (bsp_get_par_right (¬l)).
  Proof.
    intro e.
    rewrite <- complement_spec.
    setoid_rewrite get_par_right_spec.
    assert (exists y : ⌊|s∥t|⌋, y = inr e) as (y & Ey) by (exists (inr e);reflexivity).
    rewrite <- Ey at 2.
    rewrite <- (@complement_spec (PomType ⟦ bsp_par s t ⟧) y l).
    rewrite Ey;tauto.
  Qed.

  Lemma bsp_clean_get_elt (s : bsp_terms X) : is_bsp_clean s -> ⌊|s|⌋.
  Proof.
    case_eq ⟨|s|⟩;[|tauto].
    intros E C;exfalso.
    apply is_bsp_clean_bsp_size in C;revert C.
    rewrite interpret_bsp_size.
    unfold size,sizePomset,size,size_type.
    rewrite E;rsimpl;lia.
  Qed.

  Definition bsp_get_box {s : bsp_terms X} : ⌊| s |⌋ -> ⌊| ▢ s |⌋ := id.
  Lemma bsp_get_seq_left_nil s t : @bsp_get_seq_left s t [] = [].
  Proof.
    unfold bsp_get_seq_left.
    transitivity (get_seq_left (map (@inr ⌊|s|⌋ ⌊|t|⌋) []));[reflexivity|].
    apply seq_proj_get_seq_r_l.
  Qed.
  Lemma bsp_get_seq_right_nil s t : @bsp_get_seq_right s t [] = [].
  Proof.
    unfold bsp_get_seq_right.
    transitivity (get_seq_right (map (@inl ⌊|s|⌋ ⌊|t|⌋) []));[reflexivity|].
    apply seq_proj_get_seq_l_r.
  Qed.
  
  Lemma bsp_get_par_left_nil s t : @bsp_get_par_left s t [] = [].
  Proof.
    unfold bsp_get_par_left.
    transitivity (get_par_left (map (@inr ⌊|s|⌋ ⌊|t|⌋) []));[reflexivity|].
    apply par_proj_get_par_r_l.
  Qed.
  Lemma bsp_get_par_right_nil s t : @bsp_get_par_right s t [] = [].
  Proof.
    unfold bsp_get_par_right.
    transitivity (get_par_right (map (@inl ⌊|s|⌋ ⌊|t|⌋) []));[reflexivity|].
    apply par_proj_get_par_l_r.
  Qed.

  Global Instance bsp_get_box_hom s : homomorphism (@bsp_get_box s) :=
    (Pomset_box_hom ⟦s⟧).

  Lemma bsp_get_box_Boxes s :
    is_bsp_clean s -> Boxes ⟦▢ s⟧ = ⟨|▢ s|⟩ :: map (map bsp_get_box) (Boxes ⟦s⟧).
  Proof. 
    intro C;apply is_bsp_clean_bsp_size in C.
    destruct (Boxes_box_spec ⟦s⟧) as [E|E].
    - rewrite interpret_bsp_size in C.
      rewrite (sizePomset_equiv E) in C.
      exfalso;revert C;clear;rsimpl;simpl.
      replace (size un) with 0 by reflexivity;lia.
    - etransitivity;[apply E|].
      unfold bsp_get_box.
      erewrite map_ext,map_id by apply map_id.
      reflexivity.
  Qed.
    
  Lemma is_bsp_clean_box_domain (s: bsp_terms X) b:
    is_bsp_clean (bsp_box s) -> b ∈ Boxes ⟦ s ⟧ -> ~ (b ≈ ⟨| s |⟩).
  Proof.
    destruct s;simpl;try tauto.
    - intros (S1&S2) B.
      apply in_app_iff in B as [B|B];apply in_map_iff in B as (β&<-&Iβ);intros E.
      + pose proof (bsp_clean_get_elt S2) as e.
        cut (inr e ∈ map inl β).
        * intro F;apply in_map_iff in F as (e'&E'&_);discriminate.
        * apply E,in_app_iff;right;apply in_map_iff;
            exists e;split;[reflexivity|apply domain_spec].
      + pose proof (bsp_clean_get_elt S1) as e.
        cut (inl e ∈ map inr β).
        * intro F;apply in_map_iff in F as (e'&E'&_);discriminate.
        * apply E,in_app_iff;left;apply in_map_iff;
            exists e;split;[reflexivity|apply domain_spec].
    - intros (S1&S2) B.
      apply in_app_iff in B as [B|B];apply in_map_iff in B as (β&<-&Iβ);intros E.
      + pose proof (bsp_clean_get_elt S2) as e.
        cut (inr e ∈ map inl β).
        * intro F;apply in_map_iff in F as (e'&E'&_);discriminate.
        * apply E,in_app_iff;right;apply in_map_iff;
            exists e;split;[reflexivity|apply domain_spec].
      + pose proof (bsp_clean_get_elt S1) as e.
        cut (inl e ∈ map inr β).
        * intro F;apply in_map_iff in F as (e'&E'&_);discriminate.
        * apply E,in_app_iff;left;apply in_map_iff;
            exists e;split;[reflexivity|apply domain_spec].
  Qed.

End s.
      
Hint Rewrite @interpret_bsp_unit @interpret_bsp_seq @interpret_bsp_par @interpret_bsp_box
  : simpl_typeclasses.

Notation " ⌊| e |⌋ " := ⌊⟦e⟧⌋.
Notation " ⟨| e |⟩ " := ⟪PomType ⟦e⟧⟫.

