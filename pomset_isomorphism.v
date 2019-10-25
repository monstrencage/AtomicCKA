Require Import PeanoNat tools algebra Bool relations.
Require Import bsp_terms pomsets bsp_pomsets.
Require Import series_parallel_pomsets.
Require Import sub_pomsets.

Section s.
  Context {X : Set}.
  Context {decX : decidable_set X}.

  Lemma sub_term_one (s : bsp_terms X) l : s ≡ 𝟭 -> s ⨡ l ≡ 𝟭.
  Proof.
    intro E;apply bsp_size_unit;apply bsp_size_unit in E.
    revert l;induction s;intro l.
    - rsimpl in E;rsimpl;rewrite IHs1,IHs2;clear IHs1 IHs2;lia.
    - rsimpl in E;rsimpl;rewrite IHs1,IHs2;clear IHs1 IHs2;lia.
    - rsimpl in E;discriminate.
    - rsimpl in E;rsimpl.
      destruct (equivalentb _ _).
      + rsimpl;assumption.
      + apply IHs,E.
    - reflexivity.
  Qed.

  Lemma is_prefix_get_seq_left (s t : bsp_terms X) (l : list ⌊|s⋅t|⌋) :
    is_prefix l -> is_prefix (bsp_get_seq_left l).
  Proof.
    intros P e1 e2 I1 I2.
    cut (inl e1 ≤[⟦s⋅t⟧] inl e2);[intro h;apply h|].
    apply P;[|intro I';apply I2];apply get_seq_left_spec;[apply I1|apply I'].
  Qed.
  Lemma is_prefix_get_seq_right (s t : bsp_terms X) (l : list ⌊|s⋅t|⌋) :
    is_prefix l -> is_prefix (bsp_get_seq_right l).
  Proof.
    intros P e1 e2 I1 I2.
    cut (inr e1 ≤[⟦s⋅t⟧] inr e2);[intro h;apply h|].
    apply P;[|intro I';apply I2];apply get_seq_right_spec;[apply I1|apply I'].
  Qed.
  Lemma is_prefix_get_par_left (s t : bsp_terms X) (l : list ⌊|s∥t|⌋) :
    is_prefix l -> is_prefix (bsp_get_par_left l).
  Proof.
    intros P e1 e2 I1 I2.
    cut (inl e1 ≤[⟦s∥t⟧] inl e2);[intro h;apply h|].
    apply P;[|intro I';apply I2];apply get_par_left_spec;[apply I1|apply I'].
  Qed.
  Lemma is_prefix_get_par_right (s t : bsp_terms X) (l : list ⌊|s∥t|⌋) :
    is_prefix l -> is_prefix (bsp_get_par_right l).
  Proof.
    intros P e1 e2 I1 I2.
    cut (inr e1 ≤[⟦s∥t⟧] inr e2);[intro h;apply h|].
    apply P;[|intro I';apply I2];apply get_par_right_spec;[apply I1|apply I'].
  Qed.
  Lemma is_isolated_get_seq_left (s t : bsp_terms X) (l : list ⌊|s⋅t|⌋) :
    is_isolated l -> is_isolated (bsp_get_seq_left l).
  Proof.
    intros P e1 e2 I1 I2.
    apply get_seq_left_spec,(P (inl e1)).
    - apply get_seq_left_spec,I1.
    - simpl;apply I2.
  Qed.
  Lemma is_isolated_get_seq_right (s t : bsp_terms X) (l : list ⌊|s⋅t|⌋) :
    is_isolated l -> is_isolated (bsp_get_seq_right l).
  Proof.
    intros P e1 e2 I1 I2.
    apply get_seq_right_spec,(P (inr e1)).
    - apply get_seq_right_spec,I1.
    - simpl;apply I2.
  Qed.
  Lemma is_isolated_get_par_left (s t : bsp_terms X) (l : list ⌊|s∥t|⌋) :
    is_isolated l -> is_isolated (bsp_get_par_left l).
  Proof.
    intros P e1 e2 I1 I2.
    apply get_par_left_spec,(P (inl e1)).
    - apply get_par_left_spec,I1.
    - simpl;apply I2.
  Qed.
  Lemma is_isolated_get_par_right (s t : bsp_terms X) (l : list ⌊|s∥t|⌋) :
    is_isolated l -> is_isolated (bsp_get_par_right l).
  Proof.
    intros P e1 e2 I1 I2.
    apply get_par_right_spec,(P (inr e1)).
    - apply get_par_right_spec,I1.
    - simpl;apply I2.
  Qed.

  Lemma is_nested_get_seq_left (s t : bsp_terms X) (l : list ⌊|s⋅t|⌋) :
    is_nested l -> is_nested (bsp_get_seq_left l).
  Proof.
    intros N b Ib;destruct (N (map inl b)) as [I|I].
    - simpl;apply in_app_iff.
      left.
      apply in_map_iff;exists b;tauto.
    - left;intros e Ie.
      apply get_seq_left_spec.
      apply I,in_map_iff;exists e;tauto.
    - right;intro e.
      destruct (I (inl e))
        as [nIe|nIe];[left|right];intro Ie;apply nIe.
      + apply in_map_iff;exists e;tauto.
      + apply get_seq_left_spec,Ie.
  Qed.
  Lemma is_nested_get_seq_right (s t : bsp_terms X) (l : list ⌊|s⋅t|⌋) :
    is_nested l -> is_nested (bsp_get_seq_right l).
  Proof.
    intros N b Ib;destruct (N (map inr b)) as [I|I].
    - simpl;apply in_app_iff.
      right.
      apply in_map_iff;exists b;tauto.
    - left;intros e Ie.
      apply get_seq_right_spec.
      apply I,in_map_iff;exists e;tauto.
    - right;intro e.
      destruct (I (inr e))
        as [nIe|nIe];[left|right];intro Ie;apply nIe.
      + apply in_map_iff;exists e;tauto.
      + apply get_seq_right_spec,Ie.
  Qed.
  Lemma is_nested_get_par_left (s t : bsp_terms X) (l : list ⌊|s∥t|⌋) :
    is_nested l -> is_nested (bsp_get_par_left l).
  Proof.
    intros N b Ib;destruct (N (map inl b)) as [I|I].
    - simpl;apply in_app_iff.
      left.
      apply in_map_iff;exists b;tauto.
    - left;intros e Ie.
      apply get_par_left_spec.
      apply I,in_map_iff;exists e;tauto.
    - right;intro e.
      destruct (I (inl e))
        as [nIe|nIe];[left|right];intro Ie;apply nIe.
      + apply in_map_iff;exists e;tauto.
      + apply get_par_left_spec,Ie.
  Qed.
  Lemma is_nested_get_par_right (s t : bsp_terms X) (l : list ⌊|s∥t|⌋) :
    is_nested l -> is_nested (bsp_get_par_right l).
  Proof.
    intros N b Ib;destruct (N (map inr b)) as [I|I].
    - simpl;apply in_app_iff.
      right.
      apply in_map_iff;exists b;tauto.
    - left;intros e Ie.
      apply get_par_right_spec.
      apply I,in_map_iff;exists e;tauto.
    - right;intro e.
      destruct (I (inr e))
        as [nIe|nIe];[left|right];intro Ie;apply nIe.
      + apply in_map_iff;exists e;tauto.
      + apply get_par_right_spec,Ie.
  Qed.

  
  Lemma sub_term_split_seq (s : bsp_terms X) (l : list ⌊|s|⌋) :
      is_prefix l -> is_nested l ->
      s ≡ s ⨡ l ⋅ s ⨡ (¬ l).
  Proof.
    revert l;induction s.
    - rsimpl in *;intros l P N;simpl.
      pose proof (IHs1 _ (is_prefix_get_seq_left s1 s2 l P)
                       (is_nested_get_seq_left s1 s2 l N)) as E1.
      pose proof (IHs2 _ (is_prefix_get_seq_right s1 s2 l P)
                       (is_nested_get_seq_right s1 s2 l N)) as E2.
      clear IHs1 IHs2.
      rewrite <- bsp_get_seq_left_complement.
      rewrite <- bsp_get_seq_right_complement.
      case_prop (not_trivial (bsp_get_seq_left l)).
      + case_eq (bsp_get_seq_right l).
        * intros E.
          rewrite complement_nil.
          rewrite sub_term_nil.
          rewrite sub_term_full.
          rsimpl.
          rewrite right_unit,(mon_assoc _).
          rewrite E1 at 1;reflexivity.
        * intros e2 L E;exfalso.
          destruct hyp as (_&e1&_&Ie1).
          cut (inr e2 ≤[⟦s1⋅s2⟧] inl e1);[simpl;tauto|].
          apply P.
          -- apply bsp_get_seq_seq_proj,in_app_iff;right.
             apply in_map_iff;exists e2;rewrite E;simpl;tauto.
          -- rewrite bsp_get_seq_seq_proj,in_app_iff.
             repeat rewrite in_map_iff.
             intros [I|I];destruct I as (x&Ex&Ix);inversion Ex;subst.
             apply Ie1,Ix.
      + apply not_trivial_neg in hyp as [F|hyp].
        * case_eq ⟨| s1 |⟩.
          -- intro Sz.
             assert (E : s1 ≡ 𝟭)
               by (apply bsp_size_unit;rewrite interpret_bsp_size;
                   unfold size,sizePomset,size,size_type;rewrite Sz;reflexivity).
             rewrite E at 1.
             repeat rewrite (sub_term_one _ _ E).
             rsimpl;repeat rewrite left_unit.
             assumption.
          -- case_eq l.
             ++ intros -> _ _ _;simpl.
                setoid_rewrite bsp_get_seq_right_nil.
                setoid_rewrite bsp_get_seq_left_nil.
                repeat rewrite complement_nil.
                repeat rewrite sub_term_nil,sub_term_full;rsimpl.
                repeat rewrite left_unit;auto.
             ++ intros [e2|e2] L -> e1 m E;exfalso.
                ** cut (e2 ∈ bsp_get_seq_left (inl e2 :: L));[rewrite F;simpl;tauto|].
                   apply get_seq_left_spec;now left.
                ** apply (P (inr e2) (inl e1));auto.
                   --- now left.
                   --- intro I;apply get_seq_left_spec in I.
                       unfold bsp_get_seq_left in F.
                       rewrite F in I;apply I.
        * assert (E : bsp_get_seq_left l ≈ ⟨|s1|⟩)
            by (symmetry;apply domain_equiv;intros ? ?;apply hyp);clear hyp.
          rewrite E,complement_full,sub_term_full,sub_term_nil;rsimpl.
          rewrite left_unit,<-(mon_assoc _).
          case_prop(not_trivial (bsp_get_seq_right l));
            [apply bsp_eq_seq;[reflexivity|assumption];auto|].
          apply not_trivial_neg in hyp as [E'|F].
          -- rewrite E',complement_nil.
             rewrite sub_term_nil,sub_term_full,left_unit;reflexivity.
          -- assert (E' : bsp_get_seq_right l ≈ ⟨|s2|⟩)
              by (symmetry;apply domain_equiv;intros ? ?;apply F);clear F.
             rewrite E',complement_full,sub_term_full,sub_term_nil;rsimpl.
             rewrite right_unit;reflexivity.
    - intros l P N;simpl.
      rewrite <- bsp_get_par_left_complement, <- bsp_get_par_right_complement.
      set (L := bsp_get_par_left l);set (M := bsp_get_par_right l).
      pose proof (IHs1 L (is_prefix_get_par_left s1 s2 l P)
                       (is_nested_get_par_left s1 s2 l N)) as ih1.
      pose proof (IHs2 M (is_prefix_get_par_right s1 s2 l P)
                       (is_nested_get_par_right s1 s2 l N)) as ih2.
      clear IHs1 IHs2.
      case_eq ⟨|s1|⟩;[|case_eq ⟨|s2|⟩].
      + intro Sz.
        assert (E : s1 ≡ 𝟭)
          by (apply bsp_size_unit;rewrite interpret_bsp_size;
              unfold size,sizePomset,size,size_type;rewrite Sz;reflexivity).
        rewrite E at 1.
        repeat rewrite (sub_term_one _ _ E).
        rsimpl;repeat rewrite left_unit.
        assumption.
      + intros Sz _ _ _.
        assert (E : s2 ≡ 𝟭)
          by (apply bsp_size_unit;rewrite interpret_bsp_size;
              unfold size,sizePomset,size,size_type;rewrite Sz;reflexivity).
        rewrite E at 1.
        repeat rewrite (sub_term_one _ _ E).
        rsimpl;repeat rewrite right_unit.
        assumption.
      + intros e2 L2 EL2 e1 L1 EL1.
        case_prop (not_trivial L);case_prop (not_trivial M).
        * exfalso.
          destruct hyp as (e1'&_&I1&_).
          destruct hyp0 as (_&e2'&_&I2).
          apply (P (inl e1') (inr e2')).
          -- apply get_par_left_spec,I1.
          -- intro I;apply I2,get_par_right_spec,I.
        * exfalso.
          apply not_trivial_neg in hyp0 as [EM|FM].
          -- destruct hyp as (e2'&_&I2&_).
             apply (P (inl e2') (inr e2)).
             ++ apply get_par_left_spec,I2.
             ++ intro I;cut (e2 ∈ M);[rewrite EM;simpl;tauto|].
                apply get_par_right_spec,I.
          -- destruct hyp as (_&e2'&_&nI2).
                apply (P (inr e2) (inl e2')).
             ++ apply get_par_right_spec.
                   apply FM.
             ++ intro I;apply nI2,get_par_left_spec,I.
        * exfalso.
          apply not_trivial_neg in hyp as [EM|FM].
          -- destruct hyp0 as (e2'&_&I2&_).
             apply (P (inr e2') (inl e1)).
             ++ apply get_par_right_spec,I2.
             ++ intro I;cut (e1 ∈ L);[rewrite EM;simpl;tauto|].
                apply get_par_left_spec,I.
          -- destruct hyp0 as (_&e2'&_&nI2).
                apply (P (inl e1) (inr e2')).
             ++ apply get_par_left_spec.
                apply FM.
             ++ intro I;apply nI2,get_par_right_spec,I.
        * apply not_trivial_neg in hyp as [EL|FL];
            apply not_trivial_neg in hyp0 as [EM|FM].
          -- rewrite EL,EM.
             repeat rewrite complement_nil,sub_term_nil,sub_term_full.
             rsimpl;repeat rewrite left_unit;reflexivity.
          -- exfalso;apply (P (inr e2) (inl e1)).
             ++ apply get_par_right_spec,FM.
             ++ intros I;cut (e1 ∈ L);[rewrite EL;simpl;tauto|].
                apply get_par_left_spec,I.
          -- exfalso;apply (P (inl e1) (inr e2)).
             ++ apply get_par_left_spec,FL.
             ++ intros I;cut (e2 ∈ M);[rewrite EM;simpl;tauto|].
                apply get_par_right_spec,I.
          -- assert (EL : L ≈ ⟨|s1|⟩)
              by (symmetry;apply domain_equiv;intros ? ?;apply FL);clear FL.
             rewrite EL,complement_full,sub_term_nil,sub_term_full.
             assert (EM : M ≈ ⟨|s2|⟩)
               by (symmetry;apply domain_equiv;intros ? ?;apply FM);clear FM.
             rewrite EM,complement_full,sub_term_nil,sub_term_full.
             rsimpl.
             repeat rewrite right_unit;auto.
    - intros [|[] l] P N.
      + rewrite complement_nil.
        rewrite sub_term_nil,sub_term_full,left_unit;reflexivity.
      + assert (EL : υ::l ≈ ⟨|bsp_var x|⟩)
          by (intros [];split;intros _;left;reflexivity).
        rewrite EL,complement_full.
        rewrite sub_term_nil,sub_term_full,right_unit;reflexivity.
    - intros l P N;simpl.
      case_prop (not_trivial l);[|case_eq ⟨|s|⟩;[|case_prop (get_box_boxes l ≈ ⟨|s|⟩)]].
      + exfalso;apply (nested_not_trival_not_box N hyp).
        rsimpl;clear IHs;intros e [<-|F];[|exfalso;apply F].
        exists ⟨|s|⟩;split;[|reflexivity].
        case_eq ⟨|s|⟩;simpl in *;[|tauto].
        destruct hyp as (e&_).
        simpl in e.
        intro F;pose proof (domain_spec e) as Ie.
        unfold interpret in F;rewrite F in Ie;apply Ie.
      + intro Sz.
        cut (forall m : list ⌊|s|⌋, m = []).
        * intros E.
          rewrite (E (get_box_boxes l)).
          rewrite (E (get_box_boxes (¬(t:=PomType (sem_bsp s))l))).
          simpl.
          cut (s ≡ 𝟭).
          -- intros ->;rsimpl.
             rewrite bsp_eq_box_unit,left_unit;auto.
          -- apply bsp_size_unit;rewrite interpret_bsp_size.
             unfold size,sizePomset,size,size_type;rewrite Sz;reflexivity.
        * intros [|e ?];[reflexivity|].
          exfalso;cut (e ∈ ⟨|s|⟩);[|apply domain_spec].
          rewrite Sz;simpl;auto.
      + intros e L EL;rewrite <- EL;clear L EL.
        replace (equivalentb _ _) with true by (symmetry;apply equivalentb_spec,hyp0).
        replace (get_box_boxes (¬ (t:=PomType (sem_bsp s)) l)) with (@nil ⌊|s|⌋).
        * replace (equivalentb _ _) with false.
          -- rewrite sub_term_nil,right_unit;reflexivity.
          -- symmetry;apply not_true_iff_false;intro E;apply equivalentb_spec in E.
             pose proof (domain_spec e) as Ie;apply E in Ie;apply Ie.
        * unfold get_box_boxes,id in *.
          case_eq (¬ l);[intros E;symmetry;apply E|].
          intros f F EF;exfalso.
          cut (f ∈ (f::F));[|now left].
          intros If;rewrite <- EF in If.
          apply complement_spec in If.
          apply If,hyp0,domain_spec.
      + intros e L EL;rewrite <- EL;clear L EL.
        apply not_trivial_neg in hyp as [E|F];
          [|exfalso;apply hyp0; split;intros _;[apply domain_spec|apply F]].
        rewrite E in *;simpl.
        unfold get_box_boxes,id;simpl.
        replace (equivalentb _ _) with false
          by (symmetry;rewrite <- not_true_iff_false,equivalentb_spec;apply hyp0).
        rewrite sub_term_nil,left_unit.
        replace (equivalentb _ _) with true;auto.
        symmetry;apply equivalentb_spec,complement_nil.
    - intros l _ _;simpl;symmetry;apply left_unit.
  Qed.
  
  Lemma sub_term_split_par (s : bsp_terms X) (l : list ⌊|s|⌋) :
    is_isolated l -> is_nested l -> 
      s ≡ (sub_term s l) ∥ (sub_term s (¬ l)).
  Proof.
    revert l;induction s.
    - intros l P N;simpl.
      rewrite <- bsp_get_seq_left_complement, <- bsp_get_seq_right_complement.
      set (L := bsp_get_seq_left l);set (M := bsp_get_seq_right l).
      pose proof (IHs1 L (is_isolated_get_seq_left s1 s2 l P)
                       (is_nested_get_seq_left s1 s2 l N)) as ih1.
      pose proof (IHs2 M (is_isolated_get_seq_right s1 s2 l P)
                       (is_nested_get_seq_right s1 s2 l N)) as ih2.
      clear IHs1 IHs2.
      case_eq ⟨|s1|⟩;[|case_eq ⟨|s2|⟩].
      + intro Sz.
        assert (E : s1 ≡ 𝟭)
          by (apply bsp_size_unit;rewrite interpret_bsp_size;
              unfold size,sizePomset,size,size_type;rewrite Sz;reflexivity).
        rewrite E at 1.
        repeat rewrite (sub_term_one _ _ E).
        rsimpl;repeat rewrite left_unit.
        assumption.
      + intros Sz _ _ _.
        assert (E : s2 ≡ 𝟭)
          by (apply bsp_size_unit;rewrite interpret_bsp_size;
              unfold size,sizePomset,size,size_type;rewrite Sz;reflexivity).
        rewrite E at 1.
        repeat rewrite (sub_term_one _ _ E).
        rsimpl;repeat rewrite right_unit.
        assumption.
      + intros e2 L2 EL2 e1 L1 EL1.
        case_prop (not_trivial L);case_prop (not_trivial M).
        * exfalso.
          destruct hyp as (e1'&_&I1&_).
          destruct hyp0 as (_&e2'&_&I2).
          apply I2,get_seq_right_spec.
          apply (P (inl e1') (inr e2')).
          -- apply get_seq_left_spec,I1.
          -- simpl;tauto.
        * exfalso.
          apply not_trivial_neg in hyp0 as [EM|FM].
          -- destruct hyp as (e2'&_&I2&_).
             cut (e2 ∈ M);[rewrite EM;tauto|].
             apply get_seq_right_spec.
             apply (P (inl e2') (inr e2)).
             ++ apply get_seq_left_spec,I2.
             ++ simpl;tauto. 
          -- destruct hyp as (_&e2'&_&nI2).
             apply nI2,get_seq_left_spec.
             apply (P (inr e2) (inl e2')).
             ++ apply get_seq_right_spec.
                apply FM.
             ++ simpl;tauto. 
        * exfalso.
          apply not_trivial_neg in hyp as [EM|FM].
          -- destruct hyp0 as (e2'&_&I2&_).
             cut (e1 ∈ L);[rewrite EM;tauto|].
             apply get_seq_left_spec.
             apply (P (inr e2') (inl e1)).
             ++ apply get_seq_right_spec,I2.
             ++ simpl;tauto. 
          -- destruct hyp0 as (_&e2'&_&nI2).
             apply nI2,get_seq_right_spec.
             apply (P (inl e1) (inr e2')).
             ++ apply get_seq_left_spec.
                apply FM.
             ++ simpl;tauto.
        * apply not_trivial_neg in hyp as [EL|FL];
            apply not_trivial_neg in hyp0 as [EM|FM].
          -- rewrite EL,EM.
             repeat rewrite complement_nil,sub_term_nil,sub_term_full.
             rsimpl;repeat rewrite left_unit;reflexivity.
          -- exfalso.
             cut (e1 ∈ L);[rewrite EL;tauto|].
             apply get_seq_left_spec,(P (inr e2) (inl e1)).
             ++ apply get_seq_right_spec,FM.
             ++ simpl;tauto.
          -- exfalso.
             cut (e2 ∈ M);[rewrite EM;tauto|].
             apply get_seq_right_spec,(P (inl e1) (inr e2)).
             ++ apply get_seq_left_spec,FL.
             ++ simpl;tauto.
          -- assert (EL : L ≈ ⟨|s1|⟩)
              by (symmetry;apply domain_equiv;intros ? ?;apply FL);clear FL.
             rewrite EL,complement_full,sub_term_nil,sub_term_full.
             assert (EM : M ≈ ⟨|s2|⟩)
               by (symmetry;apply domain_equiv;intros ? ?;apply FM);clear FM.
             rewrite EM,complement_full,sub_term_nil,sub_term_full.
             rsimpl.
             repeat rewrite right_unit;auto.
    - intros l P N;simpl.
      rewrite <- bsp_get_par_left_complement.
      rewrite <- bsp_get_par_right_complement.
      rsimpl.
      rewrite (IHs1 (bsp_get_par_left l)) at 1;
        [rewrite (IHs2 (bsp_get_par_right l)) at 3| |].
      + repeat rewrite (mon_assoc _).
        apply bsp_eq_par;[|reflexivity].
        repeat rewrite <- (mon_assoc _).
        apply bsp_eq_par;[reflexivity|].
        auto.
      + apply is_isolated_get_par_right;auto.
      + apply is_nested_get_par_right;auto.
      + apply is_isolated_get_par_left;auto.
      + apply is_nested_get_par_left;auto.
    - intros l _ _.
      destruct l as [|[]];simpl.
      + rewrite eqX_refl.
        unfold complement;simpl.
        replace (_ =?= _) with false by (symmetry;apply eqX_false;discriminate).
        rewrite left_unit;reflexivity.
      + replace (_ =?= _) with false by (symmetry;apply eqX_false;discriminate).
        unfold complement;simpl.
        rewrite eqX_refl,negb_orb;simpl.
        rewrite eqX_refl.
        rewrite right_unit.
        reflexivity.
    - intros l I N.
      case_prop (not_trivial l).
      + exfalso.
        apply (nested_not_trival_not_box N hyp).
        destruct hyp as (e&_).
        revert e;clear;intros e b [<-|F];[|exfalso;apply F].
        simpl in *.
        revert e;generalize (sem_bsp s);simpl in *;intros p e.
        case_eq ⟪PomType p⟫;rsimpl.
        * intro E;pose proof (domain_spec e) as Ie;rewrite E in Ie;exfalso;apply Ie.
        * intros x y <-.
          exists ⟪PomType p⟫;split;[tauto|reflexivity].
      + apply not_trivial_neg in hyp as [->|E].
        * rewrite complement_nil.
          rewrite sub_term_nil.
          rewrite sub_term_full.
          rewrite left_unit;reflexivity.
        * assert (El : l ≈ ⟨|bsp_box s|⟩)
            by (symmetry;apply domain_equiv;intros ? _;apply E).
          setoid_rewrite El.
          rewrite complement_full.
          rewrite sub_term_nil.
          rewrite sub_term_full.
          rewrite right_unit;reflexivity.
    - simpl;intros;symmetry;apply left_unit. 
  Qed.

  
  Theorem completeness_bsp_terms_iso (s t : bsp_terms X) : s ≡ t <-> ⟦s⟧ ≃ ⟦t⟧.
  Proof.
    split;[apply soundness_bsp_terms|].
    intros E.
    rewrite (bsp_clean_eq s) in *.
    destruct (bsp_clean_is_bsp_clean s) as [Es|Cs];
      [rewrite Es in *;
       symmetry;apply bsp_size_unit;
       rewrite interpret_bsp_size, <- (sizePomset_equiv E);
       reflexivity|].
    generalize dependent (bsp_clean s);clear s.
    intros s;revert t;induction s.
    - intros t E C.
      destruct C as (Cs1&Cs2).
      symmetry in E; destruct E as (ϕ&Iso).
      rewrite (sub_term_split_seq t (map (fun e : ⌊|s1|⌋ => ϕ (inl e)) ⟨|s1|⟩)).
      * apply bsp_eq_seq;[apply IHs1|apply IHs2];auto.
        -- rewrite sub_term_sub_pom.
           symmetry.
           assert (exists g : ⌊| s1 |⌋ ->
                         ⌊ ⟦ t ⟧ ⇂ map (fun e : ⌊|s1|⌋=> ϕ (inl e)) ⟨| s1 |⟩ ⌋,
                           bijective g /\
                         forall x, 𝒯e (g x) = ϕ (inl x)) as (g&Bijg&Ig);
             [|exists g;split].
           ++ cut (map (fun e : ⌊|s1|⌋=> ϕ (inl e)) ⟨|s1|⟩
                       ⊆ map (fun e : ⌊|s1|⌋=> ϕ (inl e)) ⟨|s1|⟩);[|reflexivity].
              intro f;apply sub_pom_make_fun in f as (g&Ig).
              pose proof (@sub_pom_T_injective _ _ ⟨|s1|⟩) as BijT.
              apply injective_size_bijective in BijT.
              ** apply bijective_inverse in BijT as (f&E1&E2).
                 exists (g ∘ f).
                 cut (forall x, 𝒯e ((g ∘ f) x) = ϕ (inl x)).
                 --- clear Ig;intro Ig.
                     split;[|apply Ig].
                     split;split.
                     +++ intros x y E.
                         pose proof (Ig x) as Ex.
                         rewrite E,Ig in Ex.
                         repeat apply is_injective in Ex.
                         subst;reflexivity.
                     +++ intros y.
                         pose proof (sub_pom_T_internal y) as Iy.
                         apply in_map_iff in Iy as (x&Ex&_).
                         exists x.
                         rewrite <- Ig in Ex.
                         apply is_injective in Ex;assumption.
                 --- intro x;unfold Basics.compose.
                     rewrite Ig;f_equal;f_equal.
                     rewrite E2;reflexivity.
              ** pose proof (sub_pom_full ⟦s1⟧) as E1. 
                 pose proof (sizePomset_equiv E1) as Len.
                 unfold size at 2,sizePomset at 2 in Len.
                 rewrite <- Len.
                 unfold sub_pom,size at 1,sizePomset;simpl.
                 reflexivity.
           ++ assumption.
           ++ intro.
              rewrite <- (@Embedding_lbl _ (⟦t⟧⇂_) ⟦t⟧ _ (sub_pom_Embedding _ _) (g a)).
              rewrite Ig,iso_Lbl.
              apply Embedding_lbl.
           ++ intros x y.
              rewrite (@Embedding_ord _ (⟦t⟧⇂_) ⟦t⟧ _ (sub_pom_Embedding _ _) _ _).
              rewrite Ig,Ig,<- iso_Ord.
              apply Embedding_ord.
           ++ split.
              ** intros b Ib.
                 apply in_map_iff in Ib as (b'&<-&Ib').
                 apply smaller_sets_singl in Ib'.
                 apply (@Embedding_box _ _ ⟦s1⋅s2⟧ _ _) in Ib'.
                 destruct (Ib' (map inl b')) as (x&Ix&Ex);[now left|].
                 destruct iso_Boxes as (B1&B2).
                 destruct (B1 (map ϕ x)) as (β&Iβ&Eβ);
                   [apply in_map_iff;exists x;tauto|].
                 apply smaller_sets_singl in Iβ.
                 rewrite <- Eβ,<-Ex,map_map in Iβ.
                 erewrite <- map_ext in Iβ by apply Ig.
                 rewrite <- map_map in Iβ.
                 apply (@Embedding_box _ _ _ _ (sub_pom_Embedding _ _) _) in Iβ.
                 apply Iβ;now left.
              ** intros b Ib.
                 apply bijective_inverse in Bijg as (f&E1&E2).
                 apply sub_pom_Boxes in Ib as (_&b'&Ib'&Eb').
                 apply iso_Boxes in Ib' as (b''&Ib''&Eb'').
                 rewrite Eb'' in Eb';clear b' Eb''.
                 apply in_map_iff in Ib'' as (b'&<-&Ib').
                 replace (Boxes ⟦ bsp_seq s1 s2 ⟧)
                   with (Boxes ⟦ s1 ⋅ s2 ⟧) in Ib' by reflexivity.
                 simpl in Ib';apply in_app_iff in Ib' as [Ib'|Ib'].
                 --- apply in_map_iff in Ib' as (β&<-&Iβ).
                     exists (map g β).
                     split;[apply in_map_iff;exists β;tauto|].
                     intro.
                     rewrite map_map in *.
                     transitivity (ϕ (inl (f x)) ∈ map (fun x : ⌊| s1 |⌋ => ϕ (inl x)) β).
                     +++ rewrite Eb'.
                         rewrite in_map_iff.
                         split.
                         *** intros Ib.
                             exists (g (f x)).
                             rewrite Ig,E2;tauto.
                         *** intros (y&Ey&Iy).
                             rewrite <- Ig,E2 in Ey.
                             apply is_injective in Ey as ->.
                             assumption.
                     +++ repeat rewrite in_map_iff;split;intros (y&Ey&Iy).
                         *** repeat apply is_injective in Ey.
                             subst;exists (f x);rewrite E2;tauto.
                         *** subst;exists y;rewrite E1;tauto.
                 --- exfalso.
                     apply in_map_iff in Ib' as (β&<-&Iβ).
                     destruct β as [|e β];[revert Iβ;clear;eapply Pomset_hnil|].
                     assert (Ie : ϕ (inr e) ∈ map ϕ (map inr (e::β)))
                       by now left.
                     apply Eb' in Ie.
                     apply in_map_iff in Ie as (x&Ex&Ix).
                     rewrite <- (E2 x),Ig in Ex.
                     apply is_injective in Ex;discriminate.
        -- rewrite sub_term_sub_pom.
           symmetry.
           setoid_replace (¬ (map (fun e  : ⌊|s2|⌋ => ϕ(inl e)) ⟨|s1|⟩))
             with (map (fun e : ⌊|s2|⌋ => ϕ (inr e)) ⟨| s2 |⟩);
             [assert (exists g : ⌊| s2 |⌋ ->
                            ⌊ ⟦ t ⟧ ⇂ map (fun e: ⌊|s2|⌋ => ϕ (inr e)) ⟨| s2 |⟩ ⌋,
                              bijective g /\
                            forall x, 𝒯e (g x) = ϕ (inr x)) as (g&Bijg&Ig);
              [|exists g;split]|].
           ++ cut (map (fun e : ⌊|s2|⌋=> ϕ (inr e)) ⟨|s2|⟩
                       ⊆ map (fun e : ⌊|s2|⌋=> ϕ (inr e)) ⟨|s2|⟩);[|reflexivity].
              intro f;apply sub_pom_make_fun in f as (g&Ig).
              pose proof (@sub_pom_T_injective _ _ ⟨|s2|⟩) as BijT.
              apply injective_size_bijective in BijT.
              ** apply bijective_inverse in BijT as (f&E1&E2).
                 exists (g ∘ f).
                 cut (forall x, 𝒯e ((g ∘ f) x) = ϕ (inr x)).
                 --- clear Ig;intro Ig.
                     split;[|apply Ig].
                     split;split.
                     +++ intros x y E.
                         pose proof (Ig x) as Ex.
                         rewrite E,Ig in Ex.
                         repeat apply is_injective in Ex.
                         subst;reflexivity.
                     +++ intros y.
                         pose proof (sub_pom_T_internal y) as Iy.
                         apply in_map_iff in Iy as (x&Ex&_).
                         rewrite <- Ig in Ex;apply is_injective in Ex as <-.
                         exists x;reflexivity.
                 --- intro x;unfold Basics.compose.
                     rewrite Ig;f_equal;f_equal.
                     rewrite E2;reflexivity.
              ** pose proof (sub_pom_full ⟦s2⟧) as E1. 
                 pose proof (sizePomset_equiv E1) as Len.
                 unfold size at 2,sizePomset at 2 in Len.
                 rewrite <- Len.
                 unfold sub_pom,size at 1,sizePomset;simpl.
                 reflexivity.
           ++ assumption.
           ++ intro.
              rewrite <- (@Embedding_lbl _ (⟦t⟧⇂_) ⟦t⟧ _ (sub_pom_Embedding _ _) (g a)).
              rewrite Ig,iso_Lbl.
              apply Embedding_lbl.
           ++ intros x y.
              rewrite (@Embedding_ord _ (⟦t⟧⇂_) ⟦t⟧ _ (sub_pom_Embedding _ _) _ _).
              rewrite Ig,Ig,<- iso_Ord.
              apply Embedding_ord.
           ++ split.
              ** intros b Ib.
                 apply in_map_iff in Ib as (b'&<-&Ib').
                 apply smaller_sets_singl in Ib'.
                 apply (@Embedding_box _ _ ⟦s1⋅s2⟧ _ _) in Ib'.
                 destruct (Ib' (map inr b')) as (x&Ix&Ex);[now left|].
                 destruct iso_Boxes as (B1&B2).
                 destruct (B1 (map ϕ x)) as (β&Iβ&Eβ);
                   [apply in_map_iff;exists x;tauto|].
                 apply smaller_sets_singl in Iβ.
                 rewrite <- Eβ,<-Ex,map_map in Iβ.
                 erewrite <- map_ext in Iβ by apply Ig.
                 rewrite <- map_map in Iβ.
                 apply (@Embedding_box _ _ _ _ (sub_pom_Embedding _ _) _) in Iβ.
                 apply Iβ;now left.
              ** intros b Ib.
                 apply bijective_inverse in Bijg as (f&E1&E2).
                 apply sub_pom_Boxes in Ib as (_&b'&Ib'&Eb').
                 apply iso_Boxes in Ib' as (b''&Ib''&Eb'').
                 rewrite Eb'' in Eb';clear b' Eb''.
                 apply in_map_iff in Ib'' as (b'&<-&Ib').
                 replace (Boxes ⟦ bsp_seq s1 s2 ⟧)
                   with (Boxes ⟦ s1 ⋅ s2 ⟧) in Ib' by reflexivity.
                 simpl in Ib';apply in_app_iff in Ib' as [Ib'|Ib'].
                 --- exfalso.
                     apply in_map_iff in Ib' as (β&<-&Iβ).
                     destruct β as [|e β];[revert Iβ;apply Pomset_hnil|].
                     assert (Ie : ϕ (inl e) ∈ map ϕ (map inl (e::β)))
                       by now left.
                     apply Eb' in Ie.
                     apply in_map_iff in Ie as (x&Ex&Ix).
                     rewrite <- (E2 x),Ig in Ex.
                     apply is_injective in Ex;discriminate.
                 --- apply in_map_iff in Ib' as (β&<-&Iβ).
                     exists (map g β).
                     split;[apply in_map_iff;exists β;tauto|].
                     intro.
                     rewrite map_map in *.
                     transitivity (ϕ (inr (f x)) ∈ map (fun x : ⌊| s2 |⌋ => ϕ (inr x)) β).
                     +++ rewrite Eb'.
                         rewrite in_map_iff.
                         split.
                         *** intros Ib.
                             exists (g (f x)).
                             rewrite Ig,E2;tauto.
                         *** intros (y&Ey&Iy).
                             rewrite <- Ig,E2 in Ey.
                             apply is_injective in Ey as ->.
                             assumption.
                     +++ repeat rewrite in_map_iff;split;intros (y&Ey&Iy).
                         *** repeat apply is_injective in Ey.
                             subst;exists (f x);rewrite E2;tauto.
                         *** subst;exists y;rewrite E1;tauto.
           ++ intro;rewrite<- complement_spec.
              repeat rewrite in_map_iff.
              split.
              ** intro h.
                 destruct (@is_surjective _ _ ϕ _ x) as ([y|y]&<-).
                 --- exfalso;apply h.
                     exists y;split;[reflexivity|apply domain_spec].
                 --- exists y;split;[reflexivity|apply domain_spec].
              ** intros (y&<-&_) (z&E&_).
                 apply is_injective in E;discriminate.
      * intros e1 e2' I1 I2.
        apply in_map_iff in I1 as (e1'&<-&I1).
        destruct (@is_surjective _ _ ϕ _ e2') as ([e2|e2]&<-).
        -- exfalso;apply I2,in_map_iff;exists e2;split;[reflexivity|apply domain_spec].
        -- rewrite <- iso_Ord;simpl;tauto.
      * intros b Ib.
        apply iso_Boxes in Ib as (b'&Iβ&E).
        setoid_rewrite E;clear E b.
        apply in_map_iff in Iβ as (b&<-&Iβ).
        replace (Boxes ⟦ bsp_seq s1 s2 ⟧)
          with (Boxes ⟦ s1 ⋅ s2 ⟧) in Iβ by reflexivity.
        simpl in Iβ;apply in_app_iff in Iβ as [Ib'|Ib'].
        --- apply in_map_iff in Ib' as (β&<-&Iβ).
            left;rewrite map_map,(@domain_incl _ β).
            reflexivity.
        --- right.
            intros e.
            case_in e (map ϕ b);[|tauto].
            apply in_map_iff in I as (e'&<-&Ib).
            right;intros Ie.
            apply in_map_iff in Ie as (e''&E&_).
            apply is_injective in E as <-.
            apply in_map_iff in Ib' as (b'&<-&_).
            apply in_map_iff in Ib as (y&E&_).
            discriminate.
    - intros t E C.
      destruct C as (Cs1&Cs2).
      symmetry in E; destruct E as (ϕ&Iso).
      rewrite (sub_term_split_par t (map (fun e : ⌊|s1|⌋ => ϕ (inl e)) ⟨|s1|⟩)).
      * apply bsp_eq_par;[apply IHs1|apply IHs2];auto.
        -- rewrite sub_term_sub_pom.
           symmetry.
           assert (exists g : ⌊| s1 |⌋ ->
                         ⌊ ⟦ t ⟧ ⇂ map (fun e : ⌊|s1|⌋=> ϕ (inl e)) ⟨| s1 |⟩ ⌋,
                           bijective g /\
                         forall x, 𝒯e (g x) = ϕ (inl x)) as (g&Bijg&Ig);
             [|exists g;split].
           ++ cut (map (fun e : ⌊|s1|⌋=> ϕ (inl e)) ⟨|s1|⟩
                       ⊆ map (fun e : ⌊|s1|⌋=> ϕ (inl e)) ⟨|s1|⟩);[|reflexivity].
              intro f;apply sub_pom_make_fun in f as (g&Ig).
              pose proof (@sub_pom_T_injective _ _ ⟨|s1|⟩) as BijT.
              apply injective_size_bijective in BijT.
              ** apply bijective_inverse in BijT as (f&E1&E2).
                 exists (g ∘ f).
                 cut (forall x, 𝒯e ((g ∘ f) x) = ϕ (inl x)).
                 --- clear Ig;intro Ig.
                     split;[|apply Ig].
                     split;split.
                     +++ intros x y E.
                         pose proof (Ig x) as Ex.
                         rewrite E,Ig in Ex.
                         repeat apply is_injective in Ex.
                         subst;reflexivity.
                     +++ intros y.
                         pose proof (sub_pom_T_internal y) as Iy.
                         apply in_map_iff in Iy as (x&Ex&_).
                         exists x.
                         rewrite <- Ig in Ex.
                         apply is_injective in Ex;assumption.
                 --- intro x;unfold Basics.compose.
                     rewrite Ig;f_equal;f_equal.
                     rewrite E2;reflexivity.
              ** pose proof (sub_pom_full ⟦s1⟧) as E1. 
                 pose proof (sizePomset_equiv E1) as Len.
                 unfold size at 2,sizePomset at 2 in Len.
                 rewrite <- Len.
                 unfold sub_pom,size at 1,sizePomset;simpl.
                 reflexivity.
           ++ assumption.
           ++ intro.
              rewrite <- (@Embedding_lbl _ (⟦t⟧⇂_) ⟦t⟧ _ (sub_pom_Embedding _ _) (g a)).
              rewrite Ig,iso_Lbl.
              apply Embedding_lbl.
           ++ intros x y.
              rewrite (@Embedding_ord _ (⟦t⟧⇂_) ⟦t⟧ _ (sub_pom_Embedding _ _) _ _).
              rewrite Ig,Ig,<- iso_Ord.
              apply Embedding_ord.
           ++ split.
              ** intros b Ib.
                 apply in_map_iff in Ib as (b'&<-&Ib').
                 apply smaller_sets_singl in Ib'.
                 apply (@Embedding_box _ _ ⟦s1∥s2⟧ _ _) in Ib'.
                 destruct (Ib' (map inl b')) as (x&Ix&Ex);[now left|].
                 destruct iso_Boxes as (B1&B2).
                 destruct (B1 (map ϕ x)) as (β&Iβ&Eβ);
                   [apply in_map_iff;exists x;tauto|].
                 apply smaller_sets_singl in Iβ.
                 rewrite <- Eβ,<-Ex,map_map in Iβ.
                 erewrite <- map_ext in Iβ by apply Ig.
                 rewrite <- map_map in Iβ.
                 apply (@Embedding_box _ _ _ _ (sub_pom_Embedding _ _) _) in Iβ.
                 apply Iβ;now left.
              ** intros b Ib.
                 apply bijective_inverse in Bijg as (f&E1&E2).
                 apply sub_pom_Boxes in Ib as (_&b'&Ib'&Eb').
                 apply iso_Boxes in Ib' as (b''&Ib''&Eb'').
                 rewrite Eb'' in Eb';clear b' Eb''.
                 apply in_map_iff in Ib'' as (b'&<-&Ib').
                 replace (Boxes ⟦ bsp_par s1 s2 ⟧)
                   with (Boxes ⟦ s1 ∥ s2 ⟧) in Ib' by reflexivity.
                 simpl in Ib';apply in_app_iff in Ib' as [Ib'|Ib'].
                 --- apply in_map_iff in Ib' as (β&<-&Iβ).
                     exists (map g β).
                     split;[apply in_map_iff;exists β;tauto|].
                     intro.
                     rewrite map_map in *.
                     transitivity (ϕ (inl (f x)) ∈ map (fun x : ⌊| s1 |⌋ => ϕ (inl x)) β).
                     +++ rewrite Eb'.
                         rewrite in_map_iff.
                         split.
                         *** intros Ib.
                             exists (g (f x)).
                             rewrite Ig,E2;tauto.
                         *** intros (y&Ey&Iy).
                             rewrite <- Ig,E2 in Ey.
                             apply is_injective in Ey as ->.
                             assumption.
                     +++ repeat rewrite in_map_iff;split;intros (y&Ey&Iy).
                         *** repeat apply is_injective in Ey.
                             subst;exists (f x);rewrite E2;tauto.
                         *** subst;exists y;rewrite E1;tauto.
                 --- exfalso.
                     apply in_map_iff in Ib' as (β&<-&Iβ).
                     destruct β as [|e β];[revert Iβ;clear;eapply Pomset_hnil|].
                     assert (Ie : ϕ (inr e) ∈ map ϕ (map inr (e::β)))
                       by now left.
                     apply Eb' in Ie.
                     apply in_map_iff in Ie as (x&Ex&Ix).
                     rewrite <- (E2 x),Ig in Ex.
                     apply is_injective in Ex;discriminate.
        -- rewrite sub_term_sub_pom.
           symmetry.
           setoid_replace (¬ (map (fun e  : ⌊|s2|⌋ => ϕ(inl e)) ⟨|s1|⟩))
             with (map (fun e : ⌊|s2|⌋ => ϕ (inr e)) ⟨| s2 |⟩);
             [assert (exists g : ⌊| s2 |⌋ ->
                            ⌊ ⟦ t ⟧ ⇂ map (fun e: ⌊|s2|⌋ => ϕ (inr e)) ⟨| s2 |⟩ ⌋,
                              bijective g /\
                            forall x, 𝒯e (g x) = ϕ (inr x)) as (g&Bijg&Ig);
              [|exists g;split]|].
           ++ cut (map (fun e : ⌊|s2|⌋=> ϕ (inr e)) ⟨|s2|⟩
                       ⊆ map (fun e : ⌊|s2|⌋=> ϕ (inr e)) ⟨|s2|⟩);[|reflexivity].
              intro f;apply sub_pom_make_fun in f as (g&Ig).
              pose proof (@sub_pom_T_injective _ _ ⟨|s2|⟩) as BijT.
              apply injective_size_bijective in BijT.
              ** apply bijective_inverse in BijT as (f&E1&E2).
                 exists (g ∘ f).
                 cut (forall x, 𝒯e ((g ∘ f) x) = ϕ (inr x)).
                 --- clear Ig;intro Ig.
                     split;[|apply Ig].
                     split;split.
                     +++ intros x y E.
                         pose proof (Ig x) as Ex.
                         rewrite E,Ig in Ex.
                         repeat apply is_injective in Ex.
                         subst;reflexivity.
                     +++ intros y.
                         pose proof (sub_pom_T_internal y) as Iy.
                         apply in_map_iff in Iy as (x&Ex&_).
                         rewrite <- Ig in Ex;apply is_injective in Ex as <-.
                         exists x;reflexivity.
                 --- intro x;unfold Basics.compose.
                     rewrite Ig;f_equal;f_equal.
                     rewrite E2;reflexivity.
              ** pose proof (sub_pom_full ⟦s2⟧) as E1. 
                 pose proof (sizePomset_equiv E1) as Len.
                 unfold size at 2,sizePomset at 2 in Len.
                 rewrite <- Len.
                 unfold sub_pom,size at 1,sizePomset;simpl.
                 reflexivity.
           ++ assumption.
           ++ intro.
              rewrite <- (@Embedding_lbl _ (⟦t⟧⇂_) ⟦t⟧ _ (sub_pom_Embedding _ _) (g a)).
              rewrite Ig,iso_Lbl.
              apply Embedding_lbl.
           ++ intros x y.
              rewrite (@Embedding_ord _ (⟦t⟧⇂_) ⟦t⟧ _ (sub_pom_Embedding _ _) _ _).
              rewrite Ig,Ig,<- iso_Ord.
              apply Embedding_ord.
           ++ split.
              ** intros b Ib.
                 apply in_map_iff in Ib as (b'&<-&Ib').
                 apply smaller_sets_singl in Ib'.
                 apply (@Embedding_box _ _ ⟦s1∥s2⟧ _ _) in Ib'.
                 destruct (Ib' (map inr b')) as (x&Ix&Ex);[now left|].
                 destruct iso_Boxes as (B1&B2).
                 destruct (B1 (map ϕ x)) as (β&Iβ&Eβ);
                   [apply in_map_iff;exists x;tauto|].
                 apply smaller_sets_singl in Iβ.
                 rewrite <- Eβ,<-Ex,map_map in Iβ.
                 erewrite <- map_ext in Iβ by apply Ig.
                 rewrite <- map_map in Iβ.
                 apply (@Embedding_box _ _ _ _ (sub_pom_Embedding _ _) _) in Iβ.
                 apply Iβ;now left.
              ** intros b Ib.
                 apply bijective_inverse in Bijg as (f&E1&E2).
                 apply sub_pom_Boxes in Ib as (_&b'&Ib'&Eb').
                 apply iso_Boxes in Ib' as (b''&Ib''&Eb'').
                 rewrite Eb'' in Eb';clear b' Eb''.
                 apply in_map_iff in Ib'' as (b'&<-&Ib').
                 replace (Boxes ⟦ bsp_par s1 s2 ⟧)
                   with (Boxes ⟦ s1 ∥ s2 ⟧) in Ib' by reflexivity.
                 simpl in Ib';apply in_app_iff in Ib' as [Ib'|Ib'].
                 --- exfalso.
                     apply in_map_iff in Ib' as (β&<-&Iβ).
                     destruct β as [|e β];[revert Iβ;apply Pomset_hnil|].
                     assert (Ie : ϕ (inl e) ∈ map ϕ (map inl (e::β)))
                       by now left.
                     apply Eb' in Ie.
                     apply in_map_iff in Ie as (x&Ex&Ix).
                     rewrite <- (E2 x),Ig in Ex.
                     apply is_injective in Ex;discriminate.
                 --- apply in_map_iff in Ib' as (β&<-&Iβ).
                     exists (map g β).
                     split;[apply in_map_iff;exists β;tauto|].
                     intro.
                     rewrite map_map in *.
                     transitivity (ϕ (inr (f x)) ∈ map (fun x : ⌊| s2 |⌋ => ϕ (inr x)) β).
                     +++ rewrite Eb'.
                         rewrite in_map_iff.
                         split.
                         *** intros Ib.
                             exists (g (f x)).
                             rewrite Ig,E2;tauto.
                         *** intros (y&Ey&Iy).
                             rewrite <- Ig,E2 in Ey.
                             apply is_injective in Ey as ->.
                             assumption.
                     +++ repeat rewrite in_map_iff;split;intros (y&Ey&Iy).
                         *** repeat apply is_injective in Ey.
                             subst;exists (f x);rewrite E2;tauto.
                         *** subst;exists y;rewrite E1;tauto.
           ++ intro;rewrite<- complement_spec.
              repeat rewrite in_map_iff.
              split.
              ** intro h.
                 destruct (@is_surjective _ _ ϕ _ x) as ([y|y]&<-).
                 --- exfalso;apply h.
                     exists y;split;[reflexivity|apply domain_spec].
                 --- exists y;split;[reflexivity|apply domain_spec].
              ** intros (y&<-&_) (z&E&_).
                 apply is_injective in E;discriminate.
      * intros e1 e2' I1 I2.
        apply in_map_iff in I1 as (e1'&<-&I1).
        destruct (@is_surjective _ _ ϕ _ e2') as ([e2|e2]&<-).
        -- apply in_map_iff;exists e2;split;[reflexivity|apply domain_spec].
        -- repeat rewrite <- iso_Ord in I2;simpl in I2;tauto.
      * intros b Ib.
        apply iso_Boxes in Ib as (b'&Iβ&E).
        setoid_rewrite E;clear E b.
        apply in_map_iff in Iβ as (b&<-&Iβ).
        replace (Boxes ⟦ bsp_par s1 s2 ⟧)
          with (Boxes ⟦ s1 ∥ s2 ⟧) in Iβ by reflexivity.
        simpl in Iβ;apply in_app_iff in Iβ as [Ib'|Ib'].
        --- apply in_map_iff in Ib' as (β&<-&Iβ).
            left;rewrite map_map,(@domain_incl _ β).
            reflexivity.
        --- right.
            intros e.
            case_in e (map ϕ b);[|tauto].
            apply in_map_iff in I as (e'&<-&Ib).
            right;intros Ie.
            apply in_map_iff in Ie as (e''&E&_).
            apply is_injective in E as <-.
            apply in_map_iff in Ib' as (b'&<-&_).
            apply in_map_iff in Ib as (y&E&_).
            discriminate.
    - intros t It _.
      rewrite (bsp_clean_eq t) in *.
      pose proof It as Sz.
      symmetry in Sz.
      apply sizePomset_equiv in Sz.
      repeat rewrite <- interpret_bsp_size in Sz.
      rsimpl in Sz.
      destruct (bsp_clean_is_bsp_clean t) as [E|C].
      + exfalso;rewrite E in Sz;rsimpl in Sz;discriminate.
      + destruct (bsp_clean t) as [t1 t2|t1 t2|y|t'|].
        * exfalso.
          rsimpl in Sz.
          destruct C as (C1&C2).
          apply is_bsp_clean_bsp_size in C1;
            apply is_bsp_clean_bsp_size in C2.
          lia.
        * exfalso.
          rsimpl in Sz.
          destruct C as (C1&C2).
          apply is_bsp_clean_bsp_size in C1;
            apply is_bsp_clean_bsp_size in C2.
          lia.
        * destruct It as (ϕ&Iso).
          pose proof (iso_Lbl υ) as E;simpl in *;subst;reflexivity.
        * exfalso.
          destruct It as (ϕ&Iso).
          destruct iso_Boxes as (hyp&_).
          revert hyp.
          replace (Boxes ⟦bsp_var x⟧) with (@nil (list ⌊|bsp_var x|⌋))by reflexivity.
          unfold ssmaller,smaller_sets.
          simpl.
          revert Sz.
          rsimpl;rewrite (interpret_bsp_size t').
          unfold size,sizePomset,size,size_type;simpl.
          unfold interpret.
          destruct ⟪ PomType (sem_bsp t') ⟫ as [|a l];[rsimpl;discriminate|].
          intros _ F.
          destruct (F (map ϕ (a :: l)));[now left|tauto].
        * exfalso;rsimpl in Sz;discriminate.
    - intros t E C'.
      assert (⟨|bsp_box s|⟩ ∈ Boxes ⟦bsp_box s⟧ /\ is_bsp_clean s
              /\ ~ ⟨|s|⟩ ∈ Boxes ⟦s⟧) as (IB1&C&IB2).
      + split;[|split].
        * apply is_bsp_clean_bsp_size in C'.
          revert C';clear.
          rewrite interpret_bsp_size.
          unfold size,sizePomset,size,size_type;rsimpl.
          destruct ⟨|s|⟩;rsimpl;[lia|tauto].
        * revert C';clear;simpl.
          destruct s;tauto.
        * intros I.
          apply (is_bsp_clean_box_domain C') in I.
          apply I;reflexivity.
      + rewrite (bsp_clean_eq t) in *.
        destruct (bsp_clean_is_bsp_clean t) as [Et|Ct].
        * exfalso.
          apply sizePomset_equiv in E.
          apply is_bsp_clean_bsp_size in C.
          rewrite interpret_bsp_size,<-sizePomset_box,<-interpret_bsp_box in C.
          rewrite <-bsp_box_box,E,Et in C.
          revert C;clear;rsimpl.
          replace (size 𝟭) with 0 by reflexivity;lia.
        * destruct E as (ϕ&Iso).
          destruct (bsp_clean t).
          -- exfalso.
             destruct Ct as (C1&C2).
             apply iso_Boxes in IB1 as (b'&Ib'&Eb').
             replace (Boxes ⟦bsp_seq b1 b2⟧) with (Boxes ⟦b1⋅b2⟧) in Ib' by reflexivity.
             simpl in Ib'.
             rewrite map_app,in_app_iff in Ib'.
             destruct Ib' as [Ib'|Ib'];rewrite map_map,in_map_iff in Ib';
               destruct Ib' as (b&<-&Ib).
             ++ pose proof (bsp_clean_get_elt C2) as e2.
                pose proof (domain_spec (ϕ (inr e2))) as F.
                apply Eb',in_map_iff in F as (x&Ex&Ix).
                eapply is_injective in Ex.
                Unshelve.
                ** subst; apply in_map_iff in Ix as (?&F&_).
                   discriminate.
                ** apply Iso.
             ++ pose proof (bsp_clean_get_elt C1) as e1.
                pose proof (domain_spec (ϕ (inl e1))) as F.
                apply Eb',in_map_iff in F as (x&Ex&Ix).
                eapply is_injective in Ex.
                Unshelve.
                ** subst; apply in_map_iff in Ix as (?&F&_).
                   discriminate.
                ** apply Iso.
          -- exfalso.
             destruct Ct as (C1&C2).
             apply iso_Boxes in IB1 as (b'&Ib'&Eb').
             simpl in Ib'.
             rewrite map_app,in_app_iff in Ib'.
             destruct Ib' as [Ib'|Ib'];rewrite map_map,in_map_iff in Ib';
               destruct Ib' as (b&<-&Ib).
             ++ pose proof (bsp_clean_get_elt C2) as e2.
                pose proof (domain_spec (ϕ (inr e2))) as F.
                apply Eb',in_map_iff in F as (x&Ex&Ix).
                eapply is_injective in Ex.
                Unshelve.
                ** subst; apply in_map_iff in Ix as (?&F&_).
                   discriminate.
                ** apply Iso.
             ++ pose proof (bsp_clean_get_elt C1) as e1.
                pose proof (domain_spec (ϕ (inl e1))) as F.
                apply Eb',in_map_iff in F as (x&Ex&Ix).
                eapply is_injective in Ex.
                Unshelve.
                ** subst; apply in_map_iff in Ix as (?&F&_).
                   discriminate.
                ** apply Iso.
          -- exfalso.
             apply iso_Boxes in IB1 as (b'&Ib'&Eb').
             apply in_map_iff in Ib' as (b&Eb&Ib).
             apply Ib.
          -- apply bsp_eq_box,IHs,C.
             exists ϕ;split. 
             ++ apply Iso.
             ++ intro;simpl.
                apply (@iso_Lbl _ _ _ _ Iso a).
             ++ intros e1 e2.
                apply (@iso_Ord _ _ _ _ Iso e1 e2).
             ++ pose proof iso_Boxes as Bx.
               replace (Boxes ⟦ bsp_box b ⟧)
                  with(Boxes ⟦ ▢ b ⟧) in Bx by reflexivity.
               replace (Boxes ⟦ bsp_box s ⟧)
                  with(Boxes ⟦ ▢ s ⟧) in Bx by reflexivity.
                rewrite bsp_get_box_Boxes in Bx by (simpl in *;destruct b;apply Ct||tauto).
                rewrite bsp_get_box_Boxes in Bx by assumption.
                unfold bsp_get_box in Bx.
                assert (R: forall A (l : list (list A)), map (map id) l = l)
                  by (intros;erewrite map_ext by apply map_id;apply map_id).
                repeat rewrite R in Bx;clear R.
                simpl in Bx.
                replace ⟪ PomType (sem_bsp b) ⟫ with ⟨|b|⟩ in Bx by reflexivity.
                replace ⟪ PomType (sem_bsp s) ⟫ with ⟨|s|⟩ in Bx by reflexivity.
                split;intros b' Ib'.
                ** apply in_map_iff in Ib' as (x&<-&Ix').
                   assert (Ix : x ∈ ( ⟨| b |⟩ :: Boxes ⟦b⟧)) by (now right).
                   apply (in_map (map ϕ)),Bx in Ix as (y&Iy&Ey).
                   exists y;split;[|assumption].
                   destruct Iy as [<-|Iy];[|tauto].
                   exfalso.
                   apply is_bsp_clean_box_domain in Ix';[|assumption].
                   apply Ix';symmetry;apply domain_equiv;intros e _.
                   cut (ϕ e ∈ (map ϕ x));[|apply Ey,domain_spec].
                   intro Ie;apply in_map_iff in Ie as (y&E&Iy).
                   apply is_injective in E as ->;assumption.
                ** assert (Ix : b' ∈ ( ⟨| s |⟩ :: Boxes ⟦s⟧)) by (now right).
                   destruct Bx as (h1&h2).
                   apply h2 in Ix as (y&[<-|Iy]&Ey).
                   --- exfalso.
                       apply is_bsp_clean_box_domain in Ib';[|assumption].
                       apply Ib';rewrite Ey.
                       symmetry;apply domain_equiv;intros e _.
                       apply in_map_iff.
                       destruct (@is_surjective _ _ ϕ _ e) as (x&<-);exists x;auto.
                   --- apply in_map_iff in Iy as (x&<-&Ix).
                       exists (map ϕ x);split;[apply in_map_iff;exists x;tauto|].
                       assumption.
          -- exfalso;apply Ct.
    - intros.
      symmetry.
      apply bsp_size_unit.
      rewrite interpret_bsp_size, <- (sizePomset_equiv E).
      reflexivity.
  Qed.

End s.
