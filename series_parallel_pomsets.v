Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools algebra Bool relations.
Require Import bsp_terms pomsets bsp_pomsets sub_pomsets.

Section max.
  Context {A : Type}.
  Context { e o : relation A}.
  Context { eq_e : Equivalence e}.
  Context { pre : PreOrder o}.
  Context { po : PartialOrder e o}.

  Proposition ex_max l :
    l <> [] -> (forall a b, a ∈ l -> b ∈ l -> o a b \/ o b a) ->
    exists m, m ∈ l /\ forall x, x ∈ l -> o x m.
  Proof.
    induction l as [|x [|y l] IHl].
    - tauto.
    - intros _ _;exists x;split;[now left|].
      intros ? [<-|F].
      + reflexivity.
      + exfalso;apply F.
    - intros _ h.
      destruct IHl as (m&Im&hm).
      + discriminate.
      + intros a b Ia Ib;apply h;now right.
      + destruct (h m x) as [hx|hx].
        * now right.
        * now left.
        * exists x;split;[now left|].
          intros a [<-|Ia];[reflexivity|].
          transitivity m;[|assumption].
          apply hm,Ia.
        * exists m;split;[now right|].
          intros a [<-|Ia];[assumption|].
          apply hm,Ia.
  Qed.
  Context {dec_o : (forall a b, DecidableProp (o a b))}.
  Proposition ex_sup l :
    l <> [] -> exists m, m ∈ l /\ forall x, x ∈ l -> o m x -> e x m.
  Proof.
    induction l as [|x [|y l] IHl].
    - tauto.
    - intros _;exists x;split;[now left|].
      intros ? [<-|F].
      + reflexivity.
      + exfalso;apply F.
    - intros _.
      destruct IHl as (m&Im&hm).
      + discriminate.
      + destruct (dec_o m x) as [hxm|hxm].
        * exists x;split;[now left|].
          intros a [<-|Ia];[reflexivity|].
          intros h;apply antisymmetry;[|assumption].
          pose proof hxm as ham.
          rewrite h in ham;rewrite (hm _ Ia ham);assumption.
        * exists m;split;[now right|].
          intros a [<-|Ia].
          -- intros h;exfalso;apply hxm,h.
          -- apply hm,Ia.
  Qed.
End max.
Arguments ex_max : clear implicits.
Arguments ex_max {A} o {pre} l.
Arguments ex_sup : clear implicits.
Arguments ex_sup {A} e o {eq_e pre po dec_o} l.

Section min.
  Context {A : Type}.
  Context { e o : relation A}.
  Context { eq_e : Equivalence e}.
  Context { pre : PreOrder o}.
  Context { po : PartialOrder e o}.
  Proposition ex_min l :
    l <> [] -> (forall a b, a ∈ l -> b ∈ l -> o a b \/ o b a) ->
    exists m, m ∈ l /\ forall x, x ∈ l -> o m x.
  Proof.
    intros h1 h2.
    apply (ex_max (Basics.flip o)) in h1 as (m&Im&hm).
    - exists m;split;[assumption|].
      intros x Ix.
      apply hm,Ix.
    - intros a b Ia Ib.
      destruct (h2 a b Ia Ib) as [h|h];[right|left];apply h.
  Qed.
  Context {dec_o : (forall a b, DecidableProp (o a b))}.
  Proposition ex_inf l :
    l <> [] -> exists m, m ∈ l /\ forall x, x ∈ l -> o x m -> e x m.
  Proof.
    intros N.
    apply (@ex_sup _ _ _ _ _ (PartialOrder_inverse po)) in N as (m&Im&hm).
    - exists m;split;[assumption|].
      intros x Ix.
      apply hm,Ix.
    - intros a b.
      destruct (dec_o b a) as [h|h];[left|right];apply h.
  Qed.

End min.
Arguments ex_min : clear implicits.
Arguments ex_min {A} o {pre} l.
Arguments ex_inf : clear implicits.
Arguments ex_inf {A} e o {eq_e pre po dec_o} l.

Section s.
  Context {X : Set}.  

  Section disj.
    Context (P : Pomset X) (sp : SP_Pomset P).
    
    Lemma Boxes_get_Maximal b : b ∈ Boxes P -> exists b' : list ⌊ P ⌋ , Maximal P b' /\ b ⊆ b'.
    Proof.
      intros Ib.
      destruct (@dec_prop_powerset_bnd _ (fun b' => b ⊆ b') (Boxes P)) as (l&hl);
        [typeclasses eauto|].
      destruct (ex_max (@incl _) l) as (m&Im&hm).
      - intros I.
        cut (b ∈ Boxes P /\ b ⊆ b).
        + rewrite <- hl,I;simpl;tauto.
        + split;[assumption|reflexivity].
      - setoid_rewrite hl. 
        intros x y (Ix&Ibx) (Iy&Iby).
        destruct (well_nested Ix Iy) as [I|[I|I]];tauto||exfalso.
        assert (exists e, e ∈ b) as (e&Ie)
            by (destruct b as [|e b];[exfalso;eapply Pomset_hnil,Ib|exists e;now left]).
        destruct (I e) as [F|F];apply F;[apply Ibx|apply Iby];apply Ie.
      - apply hl in Im.
        exists m;split;[|tauto].
        split;[tauto|].
        intros a Ia h;apply antisymmetry;[|assumption].
        apply hm,hl;split;[assumption|].
        rewrite <- h;tauto.
    Qed.

    Definition is_isolated l :=
      forall e f, e ∈ l -> e ≤[P] f \/ f ≤[P] e -> f ∈ l.
    
    Lemma DecidableProp_is_isolated l : DecidableProp (is_isolated l).
    Proof. unfold is_isolated;typeclasses eauto. Qed.

    Lemma is_isolated_alt l : is_isolated l <-> forall e f, e ∈ l -> ~ f ∈ l -> e ⫫[P] f.
    Proof.
      split.
      - intros h e f Ie If;split;intro h';apply If,(h e f);tauto.
      - intros h e f Ie [h'|h'];(case_in f l;[assumption|apply (h e f Ie) in I as (h1&h2)]);
          tauto.
    Qed.

    Instance is_isolated_proper : Proper ((@equivalent _) ==> iff) is_isolated.
    Proof. unfold is_isolated;prove_proper. Qed.
    
    Hint Resolve DecidableProp_is_isolated is_isolated_proper.

    Lemma is_isolated_neg l :
      ~ is_isolated l <-> exists e1 e2, e1 ∈ l /\ ~ e2 ∈ l /\ (e1 ≤[P] e2 \/ e2 ≤[P] e1).
    Proof.
      case_prop (exists e1 e2 : ⌊ P ⌋, e1 ∈ l /\ ~ e2 ∈ l /\ (e1 ≤[ P] e2 \/ e2 ≤[ P] e1)).
      - split;[tauto|].
        intros (e1&e2&I1&I2&F) h.
        apply I2,(h _ _ I1 F).
      - split;[|tauto].
        intro h;exfalso;apply h.
        intros e1 e2 I1 I2.
        case_in e2 l;[tauto|].
        exfalso;apply hyp;exists e1,e2;tauto.
    Qed.
    
    Definition is_prefix l :=
      forall e f, e ∈ l -> ~ f ∈ l -> e ≤[P] f.
    
    Lemma DecidableProp_is_prefix l : DecidableProp (is_prefix l).
    Proof. unfold is_prefix;typeclasses eauto. Qed.
    
    Instance is_prefix_proper : Proper ((@equivalent _) ==> iff) is_prefix.
    Proof. unfold is_prefix;prove_proper. Qed.
    
    Hint Resolve DecidableProp_is_prefix is_prefix_proper.

    Lemma is_prefix_neg l : ~ is_prefix l <-> exists e1 e2, e1 ∈ l /\ ~e2 ∈ l /\ ~ (e1 ≤[P] e2).
    Proof.
      split.
      - intros hyp.
        case_prop (exists e1 e2, e1 ∈ l /\ ~e2 ∈ l /\ ~ (e1 ≤[P] e2));[tauto|].
        exfalso;apply hyp;intros e1 e2 I1 I2.
        case_order e1 e2;[tauto|].
        exfalso;apply hyp0;exists e1,e2;tauto.
      - intros (e1&e2&I1&I2&h) hyp.
        apply h,hyp;assumption.
    Qed.
      
    Definition is_nested l :=
      forall b, b ∈ (Boxes P) -> b ⊆ l \/ (forall e, ~ e ∈ b \/ ~ e ∈ l).

    Lemma DecidableProp_is_nested l : DecidableProp (is_nested l).
    Proof. unfold is_nested;typeclasses eauto. Qed.
    
    Instance is_nested_proper : Proper ((@equivalent _) ==> iff) is_nested.
    Proof. unfold is_nested;prove_proper. Qed.
    
    Hint Resolve DecidableProp_is_nested is_nested_proper.

    Lemma not_incl_witness (l m : list ⌊P⌋) : ~ (l ⊆ m) <-> exists e, e ∈ l /\ ~ e ∈ m.
    Proof.
      rewrite <- inclb_correct,not_true_iff_false.
      unfold inclb;rewrite forallb_false_exists.
      setoid_rewrite inb_false.
      tauto.
    Qed.
      
    Lemma is_nested_neg l : ~ is_nested l <-> exists b e1 e2, b ∈ Boxes P
                                                       /\ e1 ∈ b /\ e1 ∈ l
                                                       /\ e2 ∈ b /\ ~ e2 ∈ l.
    Proof.
      split.
      - case_prop (exists b, b ∈ Boxes P
                        /\ exists e1 e2, e1 ∈ b /\ e1 ∈ l
                                   /\ e2 ∈ b /\ ~ e2 ∈ l).
        + intros _;destruct hyp as (b&?&e1&e2&h);exists b,e1,e2;tauto.
        + intros N;exfalso;apply N;intros b Ib.
          case_prop (b ⊆ l);[tauto|].
          right;intros e1.
          case_in e1 b;[|tauto].
          case_in e1 l;[|tauto].
          exfalso.
          apply not_incl_witness in hyp0 as (e2&Ib2&Il2).
          apply hyp;exists b;split;[|exists e1,e2];tauto.
      - intros (b&e1&e2&Ib&Ib1&Il1&Ib2&Il2) h.
        destruct (h b Ib) as [I|D].
        + apply Il2,I,Ib2.
        + destruct (D e1) as [F|F];apply F;assumption.
    Qed.
        
    Definition not_trivial l := exists e1 e2 : ⌊P⌋ , e1 ∈ l /\ ~ e2 ∈ l.
                                  
    Lemma DecidableProp_not_trivial l : DecidableProp (not_trivial l).
    Proof. unfold not_trivial;typeclasses eauto. Qed.
    
    Instance not_trivial_proper : Proper ((@equivalent _) ==> iff) not_trivial.
    Proof. unfold not_trivial;prove_proper. Qed.
    
    Hint Resolve DecidableProp_not_trivial not_trivial_proper.

    Lemma not_trivial_neg l :
      ~ not_trivial l <-> l = [] \/ (forall e, e ∈ l).
    Proof.
      split.
      - intros hyp.
        destruct l as [|x l];[left;reflexivity|right].
        case_prop (exists e : ⌊ P ⌋, ~ e ∈ (x :: l)).
        + exfalso;apply hyp.
          destruct hyp0 as (e&Ie).
          exists x,e;split;[left|];tauto.
        + intros e;case_in e (x::l);[tauto|].
          exfalso;apply hyp0;exists e;assumption.
      - intros [->|h];intros (e1&e2&I1&I2).
        + apply I1.
        + apply I2,h.
    Qed.

    Lemma nested_not_trival_not_box l : 
      is_nested l -> not_trivial l ->
      ~ ([⟪PomType P⟫] ≲ (Boxes P)).
    Proof.
      intros N T B.
      destruct (B ⟪PomType P⟫) as (β&Iβ&Eβ);[now left|].
      destruct (N β Iβ) as [h|h].
      - rewrite <- Eβ in h.
        apply domain_equiv in h.
        rewrite <- (not_trivial_proper h) in T.
        destruct T as (_&e&_&F);apply F,domain_spec.
      - destruct T as (e&_&Ie&_).
        destruct (h e) as [F|F];apply F.
        + apply Eβ,domain_spec.
        + assumption.
    Qed.

    Lemma exists_isolated_entails_exists_isolated_nested :
      ~ ([domain(PomType P)] ≲ (Boxes P)) ->
      (exists l, is_isolated l /\ not_trivial l) ->
      exists l, is_isolated l /\ is_nested l /\ not_trivial l.
    Proof.
      intros hD.
      intros h;cut (exists l, is_isolated l  /\ not_trivial l
                         /\ forall m, m ⊆ l -> is_isolated m -> not_trivial m -> m ≈ l);
      [clear h|].
      - intros (l&Il&Tl&Ml).
        case_prop (is_nested l);[exists l;tauto|].
        apply is_nested_neg in hyp as (b'&e1&e2&Ib'&he).
        destruct (Boxes_get_Maximal Ib') as (b&(Ib&Mb)&Ebb').
        rewrite Ebb' in he;clear b' Ib' Ebb'.
        assert (hlb : l ⊆ b).
        + destruct (@dec_prop_set _ (fun x => x ∈ l /\ x ∈ b)) as (m&hm);
            [typeclasses eauto|].
          cut (m≈l);[intros <- ?;rewrite hm;tauto|].
          apply Ml.
          * intros ?;rewrite hm;tauto.
          * intros e f Ie O.
            rewrite hm in *.
            destruct Ie as (Iel&Ieb).
            pose proof (Il _ _ Iel O) as Ifl.
            split;[assumption|].
            case_in f b;[tauto|exfalso].
            apply he.
            apply (Il f _ Ifl).
            destruct O as [O|O];[right;eapply right_atomic
                                |left;eapply left_atomic];try apply O;eauto||tauto.
          * exists e1,e2;repeat rewrite hm;tauto.
        + exists b;repeat split.
          * intros e f Ie O.
            case_in f b;[tauto|].
            apply hlb.
            apply (Il e1 f);[tauto|].
            destruct O as [O|O];[left;eapply right_atomic
                                |right;eapply left_atomic];try apply O;eauto;try tauto.
          * intros b' Ib'.
            destruct (well_nested Ib' Ib) as [W|[W|W]].
            -- tauto.
            -- apply Mb in W as ->;[left;reflexivity|assumption].
            -- tauto.
          * case_prop (not_trivial b);[tauto|].
            apply not_trivial_neg in hyp as [->|E];[simpl in *;tauto|].
            exfalso;apply hD;intros ? [<-|F];[|exfalso;apply F].
            exists b;split;[assumption|].
            apply domain_equiv;intros ? _;apply E.
      - destruct (@dec_prop_powerset_bnd _ (fun l => is_isolated l /\ not_trivial l)
                                         (𝒫 (PomType P)))
          as (L&hL);[typeclasses eauto|].
        assert (dec: forall a b : list ⟨PomType P⟩, DecidableProp (a ⊆ b))
          by typeclasses eauto.
        destruct (@ex_inf _ _ _ _ _ _ dec) with (l := L) as (l&Il&Ml).
        + intros E;destruct h as (x&hy).
          destruct (𝒫_spec x) as (y&Iy&Exy).
          rewrite Exy in hy;clear x Exy.
          cut (y ∈ L);[rewrite E;simpl;tauto|apply hL];tauto.
        + apply hL in Il as (_&hl).
          exists l;split;[tauto|];split;[tauto|].
          intros m I1 I2 I3.
          destruct (𝒫_spec m) as (y&Iy&Ey).
          rewrite Ey in *.
          apply Ml;[rewrite hL|];tauto.
    Qed.
          
    Lemma exists_prefix_entails_exists_prefix_nested :
      ~ ([domain(PomType P)] ≲ (Boxes P)) ->
      (exists l, is_prefix l /\ not_trivial l) ->
      exists l, is_prefix l /\ is_nested l /\ not_trivial l.
    Proof.
      intros hD.
      intros h;cut (exists l, is_prefix l  /\ not_trivial l
                         /\ forall m, m ⊆ l -> is_prefix m -> not_trivial m -> m ≈ l);
      [clear h|].
      - intros (l&Il&Tl&Ml).
        case_prop (is_nested l);[exists l;tauto|].
        apply is_nested_neg in hyp as (b'&e1&e2&Ib'&he).
        destruct (Boxes_get_Maximal Ib') as (b&(Ib&Mb)&Ebb').
        rewrite Ebb' in he;clear b' Ib' Ebb'.
        assert (hyp: l ⊆ b).
        + destruct (@dec_prop_set _ (fun x => x ∈ l /\ ~ x ∈ b)) as (m&hm);
            [typeclasses eauto|].
          case_prop (not_trivial m).
          * cut (m≈l).
            -- intros E;cut (~ e1 ∈ b);[|rewrite <- E,hm in he];tauto.
            -- apply Ml;auto.
               ++ intros ?;rewrite hm;tauto.
               ++ intros e f Ie O.
                  rewrite hm in *.
                  destruct Ie as (Iel&Ieb).
                  case_in f l;[|apply Il;tauto].
                  case_in f b;[clear O|tauto].
                  destruct he as (_&_&h1&h2).
                  eapply left_atomic;try apply Ib||apply h1;auto.
          * apply not_trivial_neg in hyp as [->|F].
            -- intros a Ia.
               case_in a b;[tauto|exfalso].
               case_in a (@nil ⌊P⌋);[simpl in *;tauto|].
               rewrite hm in I0;tauto.
            -- exfalso.
               pose proof (F e1) as F';apply hm in F';tauto.
        + exists b;repeat split.
          * intros e f Ie O.
            destruct he as (h1&h2&_);clear e2.
            eapply right_atomic,Il;try apply h1;auto.
          * intros b' Ib'.
            destruct (well_nested Ib' Ib) as [W|[W|W]].
            -- tauto.
            -- apply Mb in W as ->;[left;reflexivity|assumption].
            -- tauto.
          * case_prop (not_trivial b);[tauto|].
            apply not_trivial_neg in hyp0 as [->|E];[simpl in *;tauto|].
            exfalso;apply hD;intros ? [<-|F];[|exfalso;apply F].
            exists b;split;[assumption|].
            apply domain_equiv;intros ? _;apply E.
      - destruct (@dec_prop_powerset_bnd _ (fun l => is_prefix l /\ not_trivial l)
                                         (𝒫(PomType P)))
          as (L&hL);[typeclasses eauto|].
        assert (dec: forall a b : list ⌊P⌋, DecidableProp (a ⊆ b))
          by typeclasses eauto.
        destruct (@ex_inf _ _ _ _ _ _ dec) with (l := L) as (l&Il&Ml).
        + intros E;destruct h as (x&hy).
          destruct (𝒫_spec x) as (y&Iy&Exy).
          rewrite Exy in hy;clear x Exy.
          cut (y ∈ L);[rewrite E;simpl;tauto|apply hL];tauto.
        + apply hL in Il as (_&hl).
          exists l;split;[tauto|];split;[tauto|].
          intros m I1 I2 I3.
          destruct (𝒫_spec m) as (y&Iy&Ey).
          rewrite Ey in *.
          apply Ml;[rewrite hL|];tauto.
    Qed.

    Lemma nested_prefix_iso_sequential l :
      ~ ([domain(PomType P)] ≲ (Boxes P)) ->
      is_prefix l -> is_nested l -> P ≃ (P ⇂ l) ⋅ (P ⇂ ¬l).
    Proof.
      intros NB Pref WN.
      exists (fun x : ⌊(P ⇂ l) ⋅ (P ⇂ ¬l)⌋ => match x with inl e => 𝒯e e | inr e => 𝒯e e  end).
      split.
      - split;split.
        + intros [x|x] [y|y].
          * intros E;apply (@is_injective _ _ _ (@translation_injective _ _
                                                                        (NoDup_undup _)))
              in E as ->;reflexivity.
          * intros E;exfalso.
            pose proof (translation_internal y) as Iy.
            eapply complement_spec;[apply undup_equivalent,Iy|].
            rewrite <- E.
            apply undup_equivalent,translation_internal.
          * intros E;exfalso.
            pose proof (translation_internal x) as Ix.
            eapply complement_spec;[apply undup_equivalent,Ix|].
            rewrite E.
            apply undup_equivalent,translation_internal.
          * intros E;apply (@is_injective _ _ _ (@translation_injective _ _
                                                                        (NoDup_undup _)))
              in E as ->;reflexivity.
        + intros y.
          case_in y l.
          * apply undup_equivalent,translation_total in I as (e&<-).
            exists (inl e);reflexivity.
          * apply complement_spec,undup_equivalent,translation_total in I as (e&<-).
            exists (inr e);reflexivity.
      - intros [];reflexivity.
      - intros [] [];simpl.
        + reflexivity.
        + split;[|tauto].
          intros _;apply Pref.
          * apply undup_equivalent,translation_internal.
          * apply complement_spec,undup_equivalent,translation_internal.
        + split;[tauto|].
          intros F.
          pose proof (translation_internal t) as It.
          eapply complement_spec;[apply undup_equivalent,It|].
          replace (𝒯e t) with (𝒯e t0);
            [apply undup_equivalent,translation_internal|].
          apply antisymmetry;[|assumption].
          apply Pref.
         * apply undup_equivalent,translation_internal.
         * apply complement_spec,undup_equivalent,translation_internal.
        + reflexivity.
      - split.
        + intros b Ib;apply in_map_iff in Ib as (b'&<-&Ib).
          apply in_app_iff in Ib as [Ib|Ib];apply in_map_iff in Ib as (b&<-&Ib);
            apply sub_pom_Boxes in Ib as (Ib&β&Iβ&Eb').
          * eexists;split;[eassumption|].
            rewrite Eb',map_map;reflexivity.
          * eexists;split;[eassumption|].
            rewrite Eb',map_map;reflexivity.
        + intros b Ib.
          destruct (WN b Ib) as [hb|hb].
          * apply (@sub_pom_invert_boxes _ _ _ _ Ib) in hb as (b'&Ib'&Eb').
            eexists;split;[|symmetry;eassumption].
            apply in_map_iff;eexists;split;
              [|apply in_app_iff;left;apply in_map_iff;
                eexists;split;[reflexivity|eassumption]].
            rewrite map_map;reflexivity.
          * assert (hb' : b ⊆ ¬ l)
              by (intros a Ia;apply complement_spec;destruct (hb a);tauto).
            apply (@sub_pom_invert_boxes _ _ _ _ Ib) in hb' as (b'&Ib'&Eb').
            eexists;split;[|symmetry;eassumption].
            apply in_map_iff;eexists;split;
              [|apply in_app_iff;right;apply in_map_iff;
                eexists;split;[reflexivity|eassumption]].
            rewrite map_map;reflexivity.
    Qed.

    Lemma nested_isolated_iso_parallel l :
      ~ ([domain(PomType P)] ≲ (Boxes P)) ->
      is_isolated l -> is_nested l -> P ≃ (P ⇂ l) ∥ (P ⇂ (¬l)).
    Proof.
      intros NB Pref WN.
      exists (fun x : ⌊(P ⇂ l) ∥ (P ⇂ ¬l)⌋ => match x with inl e => 𝒯e e | inr e => 𝒯e e end).
      split.
      - split;split.
        + intros [x|x] [y|y].
          * intros E;apply (@is_injective _ _ _ (@translation_injective _ _
                                                                        (NoDup_undup _)))
              in E as ->;reflexivity.
          * intros E;exfalso.
            pose proof (translation_internal y) as Iy.
            eapply complement_spec;[apply undup_equivalent,Iy|].
            rewrite <- E.
            apply undup_equivalent,translation_internal.
          * intros E;exfalso.
            pose proof (translation_internal x) as Ix.
            eapply complement_spec;[apply undup_equivalent,Ix|].
            rewrite E.
            apply undup_equivalent,translation_internal.
          * intros E;apply (@is_injective _ _ _ (@translation_injective _ _
                                                                        (NoDup_undup _)))
              in E as ->;reflexivity.
        + intros y.
          case_in y l.
          * apply undup_equivalent,translation_total in I as (e&<-).
            exists (inl e);reflexivity.
          * apply complement_spec,undup_equivalent,translation_total in I as (e&<-).
            exists (inr e);reflexivity.
      - intros [];reflexivity.
      - intros [] [];simpl.
        + reflexivity.
        + split;[tauto|].
          intros F.
          eapply complement_spec,Pref;[| |left;apply F];
            apply undup_equivalent,translation_internal.
        + split;[tauto|].
          intros F.
          eapply complement_spec,Pref;[| |right;apply F];
            apply undup_equivalent,translation_internal.
        + reflexivity.
      - split.
        + intros b Ib;apply in_map_iff in Ib as (b'&<-&Ib).
          apply in_app_iff in Ib as [Ib|Ib];apply in_map_iff in Ib as (b&<-&Ib);
            apply sub_pom_Boxes in Ib as (Ib&(b'&Ib'&Eb')).
          * eexists;split;[eassumption|].
                     rewrite Eb',map_map;reflexivity.
          * eexists;split;[eassumption|].
            rewrite Eb',map_map;reflexivity.
        + intros b Ib.
          destruct (WN b Ib) as [hb|hb].
          * apply (@sub_pom_invert_boxes _ _ _ _ Ib) in hb as (b'&Ib'&Eb').
            eexists;split;[|symmetry;eassumption].
            apply in_map_iff;eexists;split;
              [|apply in_app_iff;left;apply in_map_iff;
                eexists;split;[reflexivity|eassumption]].
            rewrite map_map;reflexivity.
          * assert (hb' : b ⊆ ¬ l)
              by (intros a Ia;apply complement_spec;destruct (hb a);tauto).
            apply (@sub_pom_invert_boxes _ _ _ _ Ib) in hb' as (b'&Ib'&Eb').
            eexists;split;[|symmetry;eassumption].
            apply in_map_iff;eexists;split;
              [|apply in_app_iff;right;apply in_map_iff;
                eexists;split;[reflexivity|eassumption]].
            rewrite map_map;reflexivity.
    Qed.
    
    Proposition SP_Pomset_disjunction  :
      {⎢P⎥ <= 1} + {exists u,
                      0 < ⎢u⎥ /\ (forall b, b ∈ Boxes u -> exists e, ~ e ∈ b)
                      /\ P ≃ ▢ u}
      + {exists u v, 0 < ⎢u⎥ /\ 0 < ⎢v⎥ /\ P ≃ u ⋅ v}
      + {exists u v, 0 < ⎢u⎥ /\ 0 < ⎢v⎥ /\ P ≃ u ∥ v}.
    Proof.
      destruct (Compare_dec.le_gt_dec ⎢P⎥ 1) as [Sz|Sz];[repeat left;assumption|].
      destruct (smaller_sets_dec [domain(PomType P)] (Boxes P)) as [hB|hB].
      - left;left;right.
        set (B' := (fun l => negb (equivalentb ⟪PomType P⟫ l)) :> Boxes P).
        assert (~ [] ∈ B') as hn'
            by (unfold B';rewrite filter_In;intros (F&_);eapply Pomset_hnil,F).
        set (Q :=Build_Pomset (fun x => ℓ x) (Pomset_po P) hn').
        destruct P as [t f ? B];simpl in *.
        exists Q;simpl.
        unfold size,sizePomset,PomType in *;simpl.
        split;[lia|].
        split.
        + intros b Ib.
          unfold B' in Ib;apply filter_In in Ib as (Ib&Ne).
          case_eq (forallb (fun e => inb e b) ⟪t⟫);intro F.
          * exfalso.
            apply negb_true_iff,not_true_iff_false in Ne;apply Ne,equivalentb_spec.
            intros x;split;[|intros _;apply domain_spec].
            intros I.
            rewrite forallb_forall in F;apply F,inb_spec in I;assumption.
          * apply forallb_false_exists in F as (e&_&Ie).
            apply inb_false in Ie.
            exists e;tauto.
        + exists id;assert (EB' : match ⟪t⟫ with
                             | [] => []
                             | _ :: _ => ⟪t⟫:: B'
                             end ≃ B).
          * destruct ⟪t⟫.
            -- exfalso.
               cut ([]∈([[]] : list (list ⟨t⟩)));[|now left].
               intros F;apply hB in F as (b'&Ib'&Eb').
               destruct b' as [|x b'];[apply Pomset_hnil,Ib'|].
               cut (x∈(x::b'));[|now left].
               intros F;apply Eb' in F;apply F.
            -- replace (cons (t0::l)) with (app[t0::l]) by reflexivity.
               split.
               ++ rewrite hB;simpl.
                  apply incl_smaller_sets.
                  apply incl_app;[reflexivity|].
                  unfold B';intros a Ia;apply filter_In in Ia as (Ia&_);assumption.
               ++ intros a Ia.
                  case_eq (negb (equivalentb (t0 :: l) a));intros E.
                  ** exists a;split;[|reflexivity].
                     apply in_app_iff;right;unfold B';apply filter_In;tauto.
                  ** exists (t0::l);split;[now left|].
                     symmetry;apply equivalentb_spec,negb_false_iff,E.
          * repeat split;unfold id;simpl;auto.
            -- intros y;exists y;reflexivity.
            -- erewrite map_ext;[rewrite map_id|intros;simpl;apply map_id].
               rewrite EB';reflexivity.
            -- erewrite map_ext;[rewrite map_id|intros;simpl;apply map_id].
               rewrite EB';reflexivity.
      - cut ({exists u v : Pomset X,
                 0 < ⎢ u ⎥ /\ 0 < ⎢ v ⎥ /\ P ≃ u ⋅ v} +
             {exists u v : Pomset X ,
                 0 < ⎢ u ⎥ /\ 0 < ⎢ v ⎥ /\ P ≃ u ∥ v});[tauto|].
        case_prop (exists l : list ⌊P⌋, l ∈ 𝒫 (PomType P)
                         /\ is_isolated l /\ not_trivial l);[right|left].
        + simpl_quantif in hyp.
          apply exists_isolated_entails_exists_isolated_nested in hyp
            as (D&Is&Ne&(e1&e2&I1&I2));[|assumption].
          exists (P⇂D),(P⇂¬D);repeat split.
          * unfold sub_pom,𝒯,size at 1,sizePomset;simpl.
            rewrite bintree_of_nat_size.
            case_eq ⎢ {{D}} ⎥;[|intros;clear;lia].
            intro F;exfalso.
            unfold size,SizeList in F.
            apply length_zero_iff_nil in F.
            apply undup_equivalent in I1;rewrite F in I1;apply I1.
          * unfold sub_pom,𝒯,size at 1,sizePomset;simpl.
            rewrite bintree_of_nat_size.
            unfold size,SizeList in *.
            case_eq (length {{¬ D}});[|intros;clear;lia].
            intro F;exfalso. 
            apply length_zero_iff_nil in F.
            apply complement_spec,undup_equivalent in I2;rewrite F in I2;apply I2.
          * apply nested_isolated_iso_parallel;assumption.
        + case_prop (exists l : list ⌊P⌋, l ∈ 𝒫 (PomType P) /\ is_prefix l /\ not_trivial l).
          * simpl_quantif in hyp0.
            apply exists_prefix_entails_exists_prefix_nested in hyp0
              as (D&Is&Ne&(e1&e2&I1&I2));[|assumption].
            exists (P⇂D),(P⇂¬D);repeat split.
            -- unfold sub_pom,𝒯,size at 1,sizePomset;simpl.
               rewrite bintree_of_nat_size.
               case_eq ⎢ {{D}} ⎥;[|intros;clear;lia].
               intro F;exfalso.
               unfold size,SizeList in F.
               apply length_zero_iff_nil in F.
               apply undup_equivalent in I1;rewrite F in I1;apply I1.
            -- unfold sub_pom,𝒯,size at 1,sizePomset;simpl.
               rewrite bintree_of_nat_size.
               unfold size,SizeList in *.
               case_eq (length {{¬ D}});[|intros;clear;lia].
               intro F;exfalso. 
               apply length_zero_iff_nil in F.
               apply complement_spec,undup_equivalent in I2;rewrite F in I2;apply I2.
            -- apply nested_prefix_iso_sequential;assumption.
          * simpl_quantif in hyp.
            simpl_quantif in hyp0.
            exfalso.
            destruct (@dec_prop_set _ (fun e => forall f, f ≤[P] e -> e = f)) as (m&m__spec);
              [typeclasses eauto|].
            destruct (@dec_prop_set _ (fun e => forall f, e ≤[P] f -> e = f )) as (M&M__spec);
              [typeclasses eauto|].
            assert (pre:PreOrder(fun a b => a ≤[P] b))
              by (split;[intro;reflexivity|intro;intros;etransitivity;eassumption]).
            assert (po:PartialOrder eq (fun a b => a ≤[P] b))
              by (intros a b;split;[intros ->;split;reflexivity|];
                  unfold Basics.flip;intros (?&?);apply antisymmetry;assumption).
            assert ((exists e:⌊P⌋, True) /\ forall e, not_trivial [e]) as ((e0&_)&sngl).
            -- clear hyp hB.
               revert Sz;unfold size,sizePomset,size,size_type.
               case_eq (domain (PomType P));[rsimpl;lia|].
               intros x [|y l];[rsimpl;lia|].
               intros h _;split;[exists x;tauto|].
               intros e;exists e.
               assert (N: y <> x) by 
                   (pose proof (domain_nodup (PomType P)) as nd;
                    rewrite h,NoDup_cons_iff in nd;simpl in *;tauto).
               simpl.
               destruct_eqX e x;[exists y|exists x].
               ++ split;[|intros [->|F];[apply N|apply F]];tauto.
               ++ tauto.
            -- case_prop (not_trivial m);[case_prop (not_trivial M)|].
               ++ assert ((forall e, exists e__m, e__m ∈ m /\ e__m ≤[P] e)
                          /\ (forall e, exists e__M, e__M ∈ M /\ e ≤[P] e__M)) as (H__m&H__M).
                  ** split.
                     --- intros e.
                         destruct (@dec_prop_set _ (fun f => f ≤[P] e)) as (l__e&hl__e);
                           [typeclasses eauto|].
                         destruct (@ex_inf _ _ _ _ _ _ (fun e f : ⌊P⌋ => po_dec e f))
                           with (l:=l__e)
                           as (e__m&Ie__m&he__m).
                         +++ intro E;cut (e∈ l__e);[rewrite E;simpl;tauto|].
                             apply hl__e;reflexivity.
                         +++ exists e__m;split;[|apply hl__e,Ie__m].
                             apply m__spec.
                             intros f If;symmetry;apply he__m.
                             *** apply hl__e;etransitivity;[eassumption|apply hl__e,Ie__m].
                             *** assumption.
                     --- intros e.
                         destruct (@dec_prop_set _ (fun f => e ≤[P] f)) as (l__e&hl__e);
                           [typeclasses eauto|].
                         destruct (@ex_sup _ _ _ _ _ _ (fun e f : ⌊P⌋ => po_dec e f))
                           with (l:=l__e)
                           as (e__M&Ie__M&he__M).
                         +++ intro E;cut (e∈ l__e);[rewrite E;simpl;tauto|].
                             apply hl__e;reflexivity.
                         +++ exists e__M;split;[|apply hl__e,Ie__M].
                             apply M__spec.
                             intros f If;symmetry;apply he__M.
                             *** apply hl__e;etransitivity;[apply hl__e,Ie__M|eassumption].
                             *** assumption.
                  ** destruct (H__m e0) as (e__m&Ie__m&_);clear e0.
                     destruct (H__M e__m) as (e__M&Ie__M&I3). 
                     destruct (@dec_prop_set _ (fun e => forall f, f ∈ M ->
                                                         e__m ≤[P] f <-> e ≤[P] f))
                       as (L&hL); [typeclasses eauto|].
                     case_prop (not_trivial L).
                     --- case_prop (is_isolated L);[apply hyp;exists L;tauto|].
                         assert (hyp__Lm: forall e, e ∈ m -> e ≤[P] e__M -> e ∈ L).
                         +++ intros e Ie he.
                             apply hL;intros f If;split.
                             *** intros h.
                                 case_order e f;[tauto|].
                                 exfalso;apply sp_N_free.
                                 exists e__m,f,e,e__M;repeat split;auto.
                                 ---- intros E;apply M__spec in E as ->;auto.
                                      apply I;reflexivity.
                                 ---- intros E;apply M__spec in E as ->;auto.
                                 ---- intros E;apply M__spec in E as ->;auto.
                                 ---- intros E;apply m__spec in E as ->;auto.
                                 ---- intros E;apply m__spec in E as ->;auto.
                             *** intros I.
                                 case_order e__m f;[tauto|].
                                 exfalso;apply sp_N_free.
                                 exists e,f,e__m,e__M;repeat split;auto.
                                 ---- intros E;apply M__spec in E as ->;auto.
                                      apply I0;reflexivity.
                                 ---- intros E;apply M__spec in E as ->;auto.
                                 ---- intros E;apply M__spec in E as ->;auto.
                                 ---- intros E;apply m__spec in E as ->;auto.
                                 ---- intros E;apply m__spec in E as ->;auto.
                         +++ assert (lem : forall e f, ~ e ∈ L -> f ∈ M -> e ≤[P] f ->
                                                  e__m ≤[P] f ->
                                                  forall g, g ∈ L -> g ≤[P] e).
                             *** intros e f Ie If hef hemf g Ig.
                                 case_order g e;[tauto|].
                                 case_order e g.
                                 ---- exfalso;apply Ie,hL.
                                      rewrite hL in Ig.
                                      intros x Ix;split.
                                      ++++ intros h;transitivity g;auto.
                                           apply Ig;auto.
                                      ++++ intro y.
                                           case_order e__m e;[transitivity e;auto|].
                                           destruct (H__m e) as (e'&Ie'&he'e).
                                           assert (e'__m : e' ∈ L)
                                             by (apply hyp__Lm;auto;transitivity e;auto;
                                                 transitivity g;auto;apply Ig;auto).
                                           rewrite hL in e'__m.
                                           apply e'__m;auto.
                                           transitivity e;auto.
                                 ---- case_prop (exists k, k ∈ M /\ ~ (e ≤[P] k) /\ e__m ≤[P] k).
                                      ++++ destruct hyp5 as (k&Ik&hek&hemk).
                                           exfalso;apply sp_N_free.
                                           rewrite hL in Ig.
                                           rewrite Ig in hemk,hemf;auto.
                                           exists g,k,e,f;repeat split;auto.
                                           ----- intro F;apply M__spec in F as ->;auto.
                                           ----- intro F;apply M__spec in F as ->;auto.
                                           ----- intro F;apply M__spec in F as ->;auto.
                                      ++++ exfalso;apply Ie,hL;intros k Ik;split.
                                           **** intros h.
                                                case_order e k;[tauto|].
                                                exfalso;apply hyp5.
                                                exists k;tauto.
                                           **** intros h.
                                                case_order e__m k;[tauto|].
                                                exfalso;apply sp_N_free.
                                                exists e,k,g,f;repeat split;auto.
                                                ----- apply hL;auto.
                                                ----- intros F.
                                                apply I0;transitivity k;auto.
                                                ----- rewrite hL in Ig.
                                                rewrite <- Ig;auto.
                                                ----- intro F;apply M__spec in F as ->;auto.
                                                ----- intro F;apply M__spec in F as ->;auto.
                             *** destruct (@dec_prop_set
                                             _ (fun e => ~ e ∈ L
                                                    /\ forall f, f ∈ M -> e ≤[P] f ->
                                                           ~ (e__m ≤[P] f)))
                                 as (S&hS);[typeclasses eauto|].
                                 case_prop (not_trivial S).
                                 ---- apply hyp;exists S;split;auto.
                                      intros e f Ie [I|I].
                                      ++++ apply hS;split.
                                           **** intro If.
                                                destruct (H__M f) as (f__M&If__M&hff__M).
                                                rewrite hS in Ie;
                                                  destruct Ie as (Ie&he).
                                                apply (he f__M);auto.
                                                ----- transitivity f;auto.
                                                ----- apply hL in hff__M;auto.
                                           **** intros g Ig hfg.
                                                intro F;apply hS in Ie as (Ie&Fe).
                                                apply (Fe g);auto.
                                                transitivity f;auto.
                                      ++++ apply hS;split.
                                           **** intros If.
                                                destruct (H__M e) as (f__M&If__M&hff__M).
                                                rewrite hS in Ie;
                                                  destruct Ie as (Ie&he).
                                                apply (he f__M);auto.
                                                rewrite hL in If.
                                                apply If;auto.
                                                transitivity e;auto.
                                           **** intros g Ig hfg hemg.
                                                pose proof Ie as h.
                                                rewrite hS in h;
                                                  destruct h as (IeL&he).
                                                case_order e__m f.
                                                ----- destruct (H__M e) as (f__M&If__M&hff__M).
                                                apply (he f__M);auto.
                                                transitivity f;auto.
                                                transitivity e;auto.
                                                ----- case_order e__m e.
                                                +++++ destruct (H__M e) as (f__M&If__M&hff__M).
                                                apply (he f__M);auto.
                                                transitivity e;auto.
                                                +++++ apply sp_N_free.
                                                exists f,e,e__m,g;repeat split;auto.
                                                ***** intro E;apply m__spec in E as ->;auto.
                                                ***** intros E.
                                                apply (he g);auto.
                                                ***** intro E;apply M__spec in E as ->;auto.
                                                ***** intro E;apply m__spec in E as ->;auto.
                                 ---- apply hyp0;exists L;split;auto.
                                      intros e1 e2 I1 I2.
                                      case_prop (exists f, f ∈ M /\ e2 ≤[P] f /\ e__m ≤[P] f).
                                      ++++ destruct hyp6 as (f&hf).
                                           apply (lem e2 f);tauto.
                                      ++++ exfalso;apply hyp5.
                                           exists e2,e__m;split;rewrite hS.
                                           **** split;[assumption|].
                                                intros f If h1 h2;apply hyp6;exists f;tauto.
                                           **** intros (_&F).
                                                apply (F e__M);tauto.
                     --- apply not_trivial_neg in hyp3 as [E|E].
                         +++ cut (e__m ∈ L);[rewrite E;simpl;tauto|].
                             apply hL;tauto.
                         +++ assert (sngl__M : forall e, e ∈ M -> e = e__M).
                             *** intros e Ie.
                                 apply M__spec;[assumption|].
                                 apply hL;auto.
                             *** destruct (@dec_prop_set _ (fun e => e<>e__M))
                                 as (L'&hL');[typeclasses eauto|].
                                 apply hyp0;exists L';split.
                                 ---- intros x y Ix Iy.
                                      destruct (H__M x) as (z&Iz&Ez).
                                      apply sngl__M in Iz as ->.
                                      destruct_eqX y e__M;[assumption|].
                                      exfalso;apply Iy,hL',N.
                                 ---- exists e__m,e__M.
                                      split;rewrite hL';[|tauto].
                                      intros ->.
                                      apply hyp;exists [e__M];split;auto.
                                      intros ? ? [<-|F] I;[left|exfalso;apply F].
                                      destruct I as [I|I].
                                      ++++ apply M__spec;auto.
                                      ++++ apply m__spec;auto.
               ++ apply not_trivial_neg in hyp2 as [->|h].
                  ** destruct (@ex_sup _ _ _ _ _ _ (fun e f : ⌊P⌋ => po_dec e f))
                       with (l:=⟪PomType P⟫) as (x0&_&hx0).
                     --- intro E;cut (e0∈ ⟪PomType P⟫);[rewrite E;simpl;auto
                                                       |apply domain_spec].
                     --- cut (x0 ∈ []);[simpl;tauto|].
                         apply M__spec;intros x hx;symmetry;apply hx0,hx;apply domain_spec.
                  ** apply hyp;exists [e0];split;auto.
                     intros ? f [<-|F] hf;[left|exfalso;apply F].
                     destruct hf as [hf|hf].
                     --- apply M__spec,hf;auto.
                     --- symmetry;apply M__spec,hf;auto.
               ++ apply not_trivial_neg in hyp1 as [->|h].
                  ** destruct (@ex_inf _ _ _ _ _ _ (fun e f : ⌊P⌋ => po_dec e f))
                       with (l:=⟪PomType P⟫) as (x0&_&hx0).
                     --- intro E;cut (e0∈⟪PomType P⟫);
                           [rewrite E;simpl;auto|apply domain_spec].
                     --- cut (x0 ∈ []);[simpl;tauto|].
                         apply m__spec;intros x hx;symmetry;apply hx0,hx;apply domain_spec.
                  ** apply hyp;exists [e0];split;auto.
                     intros ? f [<-|F] hf;[left|exfalso;apply F].
                     destruct hf as [hf|hf].
                     --- symmetry;apply m__spec,hf;auto.
                     --- apply m__spec,hf;auto.
    Qed.
        
  End disj.

  Lemma SP_Pomset_small_size (P : Pomset X) : ⎢P⎥ <= 1 -> exists s, P ≃ ⟦s⟧.
  Proof.
    case_eq ⎢P⎥;[|intros [];[|lia]];intros hyp _.
    - exists 𝟭;apply size_0_eq_unit,hyp.
    - apply size_1_eq_atomic in hyp as (x&[Ex|Ex]).
      + exists (bsp_var x);apply Ex.
      + exists (▢ (bsp_var x));apply Ex.
  Qed.

  Definition box_size (P : Pomset X) := ⎢undupEq (Boxes P)⎥.

  
  Lemma box_size_equiv P Q : P ≃ Q -> box_size P = box_size Q.
  Proof.
    cut (forall t (l m : list (list (type t))),
            l ≲ m -> ⎢undupEq l⎥ <= ⎢m⎥).
    - intros hyp E;apply antisymmetry.
      + rewrite (UndupBoxes_eq Q) in E.
        pose proof E as (f&Iso).
        pose proof (@iso_Boxes _ _ _ _ Iso) as (h1&h2). 
        apply hyp in h2;rsimpl in h2.
        rewrite h2;clear.
        unfold box_size;destruct Q;simpl;reflexivity.
      + rewrite (UndupBoxes_eq P) in E.
        pose proof E as (f&Iso).
        pose proof (@iso_Boxes _ _ _ _ Iso) as (h1&h2). 
        apply hyp in h1;rewrite undupEq_map in h1 by typeclasses eauto;rsimpl in h1.
        rewrite h1;clear.
        unfold box_size;destruct P;simpl;reflexivity.
    - intros t l;induction l;intros m;[rsimpl;lia|].
      intros hyp;simpl.          
      case_eq (forallb (fun b => negb(equivalentb a b)) l);intro E.
      + rsimpl.
        rewrite forallb_forall in E.
        setoid_rewrite negb_true_iff in E.
        setoid_rewrite <- not_true_iff_false in E.
        setoid_rewrite equivalentb_spec in E.
        assert (hyp' : l ≲ ((fun l => negb (equivalentb a l)) :> m)).
        * intros b Ib.
          cut (b ∈ (a :: l));[|now right].
          intros Ib';apply hyp in Ib' as (b'&Ib'&Eb');exists b'.
          split;[|assumption].
          apply filter_In;split;[assumption|].
          apply negb_true_iff,not_true_iff_false.
          rewrite equivalentb_spec,<-Eb';apply E,Ib.
        * etransitivity;[apply Le.le_n_S, (IHl _ hyp')|].
          cut (a ∈ (a :: l));[|now left].
          intros Ia';apply hyp in Ia' as (a'&Ia'&Ea').
          apply filter_length_lt with (a0:=a');[assumption|].
          apply negb_false_iff,equivalentb_spec,Ea'.
      + apply IHl.
        intros b Ib.
        cut (b ∈ (a :: l));[|now right].
        intros Ib';apply hyp in Ib' as (b'&Ib'&Eb');exists b';tauto.
  Qed.      

  Lemma sizePomset_box Y (P : Pomset Y) : ⎢▢ P⎥ = ⎢P⎥.
  Proof. destruct P;reflexivity. Qed.

  Lemma sizePomset_seq Y (P Q : Pomset Y) : ⎢P⋅Q⎥ = ⎢P⎥+⎢Q⎥.
  Proof. destruct P,Q;unfold size,sizePomset;simpl;apply size_node. Qed.
  
  Lemma sizePomset_par Y (P Q : Pomset Y) : ⎢P∥Q⎥ = ⎢P⎥+⎢Q⎥.
  Proof. destruct P,Q;unfold size,sizePomset;simpl;apply size_node. Qed.

  
  Lemma box_size_seq P Q : box_size (P⋅Q) = box_size P+box_size Q.
  Proof.
    destruct P as [t f O B po hn],Q as [t' f' O' B' po' hn'];unfold box_size;simpl;rsimpl.
    transitivity ⎢ undupEq (map (map inl) B : list (list (type (node t t'))))
                 ++ undupEq (map (map inr) B' : list (list (type (node t t')))) ⎥.
    - revert hn';f_equal;simpl;clear;intro.
      induction B;simpl;[reflexivity|].
      case_eq (forallb (fun b : list (type t + type t') => negb (equivalentb (map inl a) b))
                       (map (map inl) B)).
      + intros E.
        rewrite forallb_forall in E.
        setoid_rewrite negb_true_iff in E.
        setoid_rewrite <-not_true_iff_false in E.
        setoid_rewrite equivalentb_spec in E.
        replace (forallb _ _) with true;[replace (forallb _ _) with true;rsimpl;
                                         [rewrite IHB;rsimpl;reflexivity|]|];
        symmetry;apply forallb_forall;intros l Il;apply negb_true_iff,not_true_iff_false;
          rewrite equivalentb_spec.
        * apply E,Il.
        * apply in_app_iff in Il as [Il|Il];[apply E,Il|].
          apply in_map_iff in Il as (m&<-&Im).
          intros EE.
          destruct m as [|x m];[apply hn',Im|].
          cut ((inr x : type (node t t')) ∈ (map inr (x::m)));[|now left].
          intros hyp;apply EE,in_map_iff in hyp as (?&F&_);discriminate.
      + intros E.
        apply forallb_false_exists in E as (x&Ix&Ex).
        apply in_map_iff in Ix as (b&<-&Ib).
        apply negb_false_iff,equivalentb_spec in Ex.
        replace (forallb _ _) with false;[replace (forallb _ _) with false;rsimpl;
                                          [rewrite IHB;rsimpl;reflexivity|]|];
        symmetry;apply forallb_false_exists;exists (map inl b);
          [|rewrite in_app_iff];split;try left;
            (apply in_map_iff;exists b;tauto)
            || (apply negb_false_iff,equivalentb_spec,Ex).
    - rsimpl.
      repeat rewrite undupEq_map by (split;intros ? ? E;inversion E;subst;reflexivity).
      rsimpl;reflexivity.
  Qed.
  
  Lemma box_size_par P Q : box_size (P∥Q) = box_size P+box_size Q.
  Proof.
    pose proof (box_size_seq P Q) as hyp;revert hyp.
    destruct P,Q;unfold box_size;simpl;rsimpl;tauto.
  Qed.
  
  Theorem bsp_pomsets_iff_SP_Pomset :
    forall P : Pomset X, (exists d : SP_Pomset P, True) <-> exists s, P ≃ ⟦s⟧.
  Proof.
    intros P;split.
    - remember (⎢P⎥ + box_size P) as N.
      assert (hyp : ⎢P⎥ + box_size P <= N) by lia;clear HeqN.
      intros (sp&_).
      revert P hyp sp;induction N.
      + intros P hyp _;exists 𝟭.
        apply size_0_eq_unit.
        revert hyp.
        generalize (box_size P);generalize ⎢P⎥;intros ? ?;lia.
      + intros P hyp SP.
        destruct (SP_Pomset_disjunction SP) as
            [[[h|(u&hu&hub&E)]|(u&v&hu&hv&E)]|(u&v&hu&hv&E)].
        * apply SP_Pomset_small_size,h.
        * pose proof E as (f & Iso__f).
          destruct (IHN u) as (s&Es).
          -- pose proof (box_size_equiv E) as len1.
             pose proof (sizePomset_equiv E) as len2.
             cut (⎢u⎥ = ⎢▢ u⎥ /\ box_size (▢ u) = S (box_size u));
               [intros (->&E');rewrite E' in len1;rewrite len1,len2 in hyp;
                revert hyp;clear;lia|].
             split;[destruct u;reflexivity|].
             revert hu hub;clear.
             destruct u as [t f O B po hn];unfold box,box_size;simpl.
             case_eq ⟪t⟫;simpl.
             ++ intros D L;exfalso.
                unfold size,sizePomset,size,size_type in L;simpl in L.
                rewrite D in L;rsimpl in L;lia.
             ++ intros t' l' Etl _ hub.
                case_eq (forallb (fun b => negb (equivalentb (t' :: l') b)) B).
                ** rsimpl;reflexivity.
                ** intros F;exfalso;apply forallb_false_exists in F as (L&hL&N).
                   apply negb_false_iff,equivalentb_spec in N.
                   destruct (hub _ hL) as (e&nIe);apply nIe.
                   rewrite <- N,<-Etl;apply domain_spec.
          -- apply SP_Pomset_box_rev,(SP_Pomset_equiv (exist _ _ Iso__f)),SP.
          -- exists (▢ s);rsimpl.
             rewrite E,<-Es;reflexivity.
        * pose proof E as (f&Iso__f).
          destruct (IHN u) as (s&Es);[| |destruct (IHN v) as (t&Et)].
          -- pose proof (box_size_equiv E) as len1.
             pose proof (sizePomset_equiv E) as len2.
             rsimpl in *.
             apply box_size_equiv in E.
             rewrite box_size_seq in len1.
             rewrite sizePomset_seq in len2.
             revert hyp len1 len2 hv;clear;lia.
          -- eapply SP_Pomset_seq_left,(SP_Pomset_equiv (exist _ _ Iso__f)),SP.
          -- pose proof (box_size_equiv E) as len1.
             pose proof (sizePomset_equiv E) as len2.
             rsimpl in *.
             apply box_size_equiv in E.
             rewrite box_size_seq in len1.
             rewrite sizePomset_seq in len2.
             revert hyp len1 len2 hu;clear;lia.
          -- eapply SP_Pomset_seq_right,(SP_Pomset_equiv (exist _ _ Iso__f)),SP.
          -- exists (s⋅t);rsimpl.
             rewrite E,Es,Et;reflexivity.
        * pose proof E as (f&Iso__f).
          destruct (IHN u) as (s&Es);[| |destruct (IHN v) as (t&Et)].
          -- pose proof (box_size_equiv E) as len1.
             pose proof (sizePomset_equiv E) as len2.
             rsimpl in *.
             apply box_size_equiv in E.
             rewrite box_size_par in len1.
             rewrite sizePomset_par in len2.
             revert hyp len1 len2 hv;clear;lia.
          -- eapply SP_Pomset_par_left,(SP_Pomset_equiv (exist _ _ Iso__f)),SP.
          -- pose proof (box_size_equiv E) as len1.
             pose proof (sizePomset_equiv E) as len2.
             rsimpl in *.
             apply box_size_equiv in E.
             rewrite box_size_par in len1.
             rewrite sizePomset_par in len2.
             revert hyp len1 len2 hu;clear;lia.
          -- eapply SP_Pomset_par_right,(SP_Pomset_equiv (exist _ _ Iso__f)),SP.
          -- exists (s∥t);rsimpl.
             rewrite E,Es,Et;reflexivity.
    - intros (s&Es);pose proof (bsp_pomsets_SP_pomsets s) as h.
      symmetry in Es.
      destruct Es as (f&I).
      assert (h' : { ϕ : ⌊P⌋ -> ⌊⟦s⟧⌋ | isomorphism ϕ})
        by (exists f;apply I).
      exists (SP_Pomset_equiv h' h);tauto.
  Qed.

End s.
