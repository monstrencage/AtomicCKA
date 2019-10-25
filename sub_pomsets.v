Require Import PeanoNat tools algebra Bool relations.
Require Import bsp_terms pomsets bsp_pomsets.
(* Require Import series_parallel_pomsets. *)

Section s.
  Context {X : Set}.
  Context {decX : decidable_set X}.
  Section sub_pomsets.
    Context {P : Pomset X} {D : list ⌊P⌋}.

    Definition sub_pom_box := (fun b => existsb (fun b' => equivalentb b' (map (𝒯l {{D}}) b))
                                             (Boxes P))
                                :> 𝒫 (𝒯 {{D}}).

    Lemma sub_pom_box_spec b :
      b ∈ sub_pom_box <-> b ∈ 𝒫 (𝒯 {{D}}) /\ exists a, a ∈ Boxes P /\ a ≈ map (𝒯l {{D}}) b.
    Proof.
      unfold sub_pom_box.
      setoid_rewrite filter_In.
      setoid_rewrite existsb_exists.
      setoid_rewrite equivalentb_spec.
      reflexivity.
    Qed.
    
    Lemma sub_pom_list_incl b : map (𝒯l {{D}}) b ⊆ D.
    Proof.
      intros x Ix;apply in_map_iff in Ix as (y&<-&Iy).
      apply undup_equivalent,translation_internal.
    Qed.

    Lemma sub_pom_hnil : ~ [] ∈ sub_pom_box.
    Proof.
      rewrite sub_pom_box_spec.
      intros (_&(x&h&E)).
      destruct x as [|a x];[|cut (a∈[]);[simpl;tauto|apply E;now left]].
      simpl in *;eapply Pomset_hnil,h.
    Qed.

    Definition sub_pom : Pomset X.
    Proof.
      apply (@Build_Pomset X (𝒯{{D}}) (fun x => ℓ (𝒯e x)) (fun x y => 𝒯e x ≤[P] 𝒯e y)
                           sub_pom_box).
      - split;intro;intros;simpl.
        + reflexivity.
        + etransitivity;eassumption.
        + now apply (@is_injective _ _ _(translation_injective
                                           (NoDup_undup _))),antisymmetry.
      - apply sub_pom_hnil.
    Defined.
    
    Corollary sub_pom_Boxes b :
      b ∈ Boxes sub_pom <-> b ∈ 𝒫 (PomType sub_pom)
                          /\ exists a, a ∈ Boxes P /\ a ≈ map (𝒯l {{D}}) b.
    Proof. apply sub_pom_box_spec. Qed.
    
    Lemma sub_pom_invert_list b :
      b ⊆ D -> exists b' : list ⌊ sub_pom ⌋ , map (𝒯l {{D}}) b' = b .
    Proof.
      induction b.
      - intros _;exists [];reflexivity.
      - intros I;destruct IHb as (b'&<-);[intros ? ?;apply I;now right|].
        assert (Ia : a ∈ {{D}}) by (apply undup_equivalent,I;now left).
        destruct (translation_total Ia) as (a'&<-).
        exists (a'::b');simpl;reflexivity.
    Qed.
    
    Lemma sub_pom_invert_boxes b :
      b ∈ Boxes P -> b ⊆ D ->
      exists b' : list ⌊ sub_pom ⌋ , b' ∈ Boxes sub_pom /\ map (𝒯l {{D}}) b' ≈ b .
    Proof.
      intros Ib Incl.
      destruct (sub_pom_invert_list _ Incl) as (b'&<-).
      destruct (𝒫_spec b') as (b&Ib'&Eb).
      setoid_rewrite Eb;exists b;split;[|reflexivity].
      apply sub_pom_box_spec;split;[assumption|].
      setoid_rewrite <- Eb;eexists;split;[eassumption|reflexivity].
    Qed.

    Lemma sub_pom_T_internal (a : ⌊sub_pom⌋) : 𝒯e a ∈ D.
    Proof. apply undup_equivalent,translation_internal. Qed.

    Global Instance sub_pom_T_injective : injective (𝒯l {{D}}).
    Proof. apply translation_injective,NoDup_undup. Qed.

    Lemma sub_pom_T_invert a : a ∈ D -> {b : ⌊sub_pom⌋ | 𝒯e b = a}.
    Proof. intros I;apply translation_invert,undup_equivalent,I. Qed.

  End sub_pomsets.
  Arguments sub_pom : clear implicits.
  Infix " ⇂ " := sub_pom (at level 20).
  Arguments sub_pom_box : clear implicits.

  Lemma sub_pom_make_fun_expl P Q l m f :
    map f l ⊆ m -> forall x: ⌊P⇂l⌋, {y :⌊Q⇂m⌋ | 𝒯e y = f (𝒯e x)}.
  Proof.
    intro hyp.
    intros x.
    assert (Ix : f (𝒯e x) ∈ m)
      by (apply hyp,in_map_iff;exists (𝒯e x);split;
          [reflexivity|apply sub_pom_T_internal]).
    apply sub_pom_T_invert in Ix as (y&Iy).
    exists y;assumption.
  Qed.

  Definition sub_pom_lift_fun P Q l f (x : ⌊P⇂l⌋) : {y :⌊Q⇂(map f l)⌋ | 𝒯e y = f (𝒯e x)}.
  Proof. apply (sub_pom_make_fun_expl P Q l (map f l) f);reflexivity. Qed.
  
  Lemma sub_pom_make_fun P Q l m f :
    map f l ⊆ m -> exists g : ⌊P⇂l⌋ -> ⌊Q⇂m⌋ , forall x, 𝒯e (g x) = f (𝒯e x).
  Proof.
    intro hyp.
    pose proof (sub_pom_make_fun_expl P Q l m f hyp) as G.
    exists (fun x => proj1_sig (G x)).
    intros x;destruct (G x) as (y&hy);apply hy.
  Qed.
  
  Global Instance sub_pom_proper P :
    Proper (@equivalent _ ==> sequiv) (sub_pom P).
  Proof.
    intros l m E.
    destruct (@sub_pom_make_fun P P m l id) as (f&h__f);[rewrite map_id,E;reflexivity|].
    destruct (@sub_pom_make_fun P P l m id) as (g&h__g);[rewrite map_id,E;reflexivity|].
    unfold id in *;simpl in *.
    unfold id in h__f;simpl in h__f.
    exists f;split.
    - apply bijective_inverse_iff;exists g;split;intro a;
        apply is_injective;rewrite h__g,h__f||rewrite h__f,h__g;reflexivity.
    - intro a;simpl.
      rewrite h__f;reflexivity.
    - intros a b;simpl.
      rewrite h__f,h__f;reflexivity.
    - split;intros b Ib.
      + apply in_map_iff in Ib as (c&<-&Ic).
        apply sub_pom_Boxes in Ic as (Ic&b&Ib&Eb).
        destruct (𝒫_spec (map f c)) as (b'&Ib'&Eb').
        setoid_rewrite Eb'.
        exists b';split;[|reflexivity].
        apply sub_pom_Boxes;split;[assumption|].
        exists b;split;[assumption|].
        rewrite Eb,<-Eb',map_map.
        erewrite <- map_ext;[reflexivity|apply h__f].
      + apply sub_pom_Boxes in Ib as (Ib&b'&Ib'&Eb').
        destruct (𝒫_spec (map g b)) as (b''&Ib''&Eb'').
        exists (map f b'');split. 
        * apply in_map_iff;exists b'';split;[reflexivity|].
          apply sub_pom_Boxes;split;[assumption|].
          exists b';split;[assumption|].
          rewrite Eb',<-Eb'',map_map.
          erewrite <- map_ext;[reflexivity|apply h__g].
        * rewrite <-Eb'',map_map.
          erewrite map_ext,map_id;[reflexivity|].
          intro a;apply is_injective;rewrite h__f,h__g;reflexivity.
  Qed.
  Lemma sub_pom_nil P : P ⇂ [] ≃ 𝟭.
  Proof.
    apply size_0_eq_unit.
    unfold sub_pom,size,sizePomset;reflexivity.
  Qed.

  Lemma sub_pom_full P : P ⇂ ⟪PomType P⟫ ≃ P.
  Proof.
    symmetry;exists (𝒯l {{⟪PomType P⟫}}).
    assert (B: bijective (𝒯l {{⟪PomType P⟫}})).
    - split;split;[apply is_injective|].
      intro y;apply translation_total,undup_equivalent;auto.
    - split.
      + assumption.
      + intro a;reflexivity.
      + intros a b;reflexivity.
      + split.
        * intros x Ib.
          apply in_map_iff in Ib as (b&<-&Ib).
          apply sub_pom_Boxes in Ib as (Ib&b'&Ib'&E).
          exists b';split;[|symmetry];tauto.
        * intros b Ib.
          destruct (sub_pom_invert_boxes _ Ib (@domain_incl _ _)) as (b'&Ib'&E).
          exists (map (𝒯l {{⟪ PomType P ⟫}}) b');split;[|symmetry;assumption].
          apply in_map_iff;exists b';tauto.
  Qed.

  
  Class Embedding (P Q : Pomset X) inclusion_map :=
    {
      Embedding_inj :> injective inclusion_map;
      Embedding_lbl : forall a, ℓ (inclusion_map a) = ℓ a;
      Embedding_ord : forall a a', a ≤[ P] a' <-> inclusion_map a ≤[ Q] inclusion_map a';
      Embedding_box : forall b, [b] ≲ Boxes P <-> [map inclusion_map b] ≲ Boxes Q 
    }.  
        
  Global Instance Embedding_id P : Embedding P P id.
  Proof.
    split.
    - split;unfold id;tauto.
    - reflexivity.
    - reflexivity.
    - intro;rewrite map_id;reflexivity.
  Qed.

  Global Instance Embedding_iso P Q (ϕ : ⌊P⌋ -> ⌊Q⌋) : isomorphism ϕ -> Embedding P Q ϕ.
  Proof.
    intros Iso;split.
    - apply Iso.
    - apply Iso.
    - apply Iso.  
    - pose proof (@iso_Boxes _ _ _ _ Iso) as EB.
      intro;rewrite <- EB.
      split.
      + intros h ? [<-|F];[|exfalso;tauto].
        destruct (h b) as (b'&Ib'&Eb');[now left|].
        exists (map ϕ b');split;[|rewrite Eb';reflexivity].
        apply in_map_iff;exists b';tauto.
      + intros h ? [<-|F];[|exfalso;tauto].
        destruct (h (map ϕ b)) as (b''&Ib'&Eb');[now left|].
        apply in_map_iff in Ib' as (b'&<-&Ib').
        exists b';split;[assumption|].
        erewrite <- map_id,map_ext,<-map_map,<-Eb',map_map,map_ext,map_id.
        * reflexivity.
        * simpl;apply inverse_elim1.
        * intro;symmetry;apply inverse_elim1.
  Qed.
  
  Global Instance Embedding_compose P Q R f g :
    Embedding P Q f -> Embedding Q R g -> Embedding P R (g∘f).
  Proof.
    intros E1 E2.
    unfold Basics.compose;split.
    - apply injective_compose;apply Embedding_inj.
    - intros;repeat rewrite Embedding_lbl;reflexivity.
    - intros;repeat rewrite <- Embedding_ord;reflexivity.
    - intros;rewrite <- map_map;repeat rewrite <-Embedding_box.
      reflexivity.
  Qed.

  Lemma Embedding_is_sub_pom P Q ι : Embedding P Q ι -> P ≃ Q ⇂ (map ι ⟪PomType P⟫).
  Proof.
    intros Emb.
    rewrite <- sub_pom_full at 1.
    destruct (@sub_pom_make_fun P Q ⟪PomType P⟫ (map ι ⟪PomType P⟫) ι)
      as (f&h__f);[reflexivity|].
    symmetry;exists f;split.
    - split;split.
      + intros x y E.
        apply (@is_injective _ _ (𝒯l _));[typeclasses eauto|].
        apply Embedding_inj.
        rewrite <- h__f,E,h__f;reflexivity.
      + intros y.
        pose proof (sub_pom_T_internal y) as Iy.
        apply in_map_iff in Iy as (x'&Ex&Ix).
        apply sub_pom_T_invert in Ix as (x&<-).
        exists x;rewrite <- h__f in Ex;apply is_injective in Ex;assumption.
    - intros a;simpl.
      rewrite h__f,Embedding_lbl;reflexivity.
    - intros a b;simpl.
      rewrite h__f,h__f,Embedding_ord;reflexivity.
    - split;intros b Ib.
      + apply in_map_iff in Ib as (b'&<-&Eb').
        apply sub_pom_Boxes in Eb' as (Ib'&b&Ib&Eb).
        assert (I : [b] ≲ Boxes P)
          by (intros ? [<-|F];[exists b;split;[assumption|reflexivity]
                                |exfalso;apply F]).
        apply Embedding_box in I as (β&Iβ&Eβ);[now left|].
        assert (hβ : β ⊆ map ι ⟪ PomType P ⟫)
          by (rewrite <- Eβ,<-domain_incl;reflexivity).
        apply (sub_pom_invert_boxes _ Iβ) in hβ as (α&Iα&Eα).
        exists α;split;[assumption|].
        rewrite <- Eβ,Eb,map_map in Eα.
        erewrite <- (map_ext _ _ h__f) in Eα.
        intro a;transitivity (𝒯e a ∈ map (𝒯l {{map ι ⟪ PomType P ⟫}}) α).
        * rewrite Eα;split;intros I;apply in_map_iff in I as (x&Ex&Ix);
            apply in_map_iff.
          -- subst;exists x;tauto.
          -- apply is_injective in Ex as <-.
             exists x;tauto.
        * split;intros I.
          -- apply in_map_iff in I as (x&Ex&Ix).
             apply is_injective in Ex as ->;assumption.
          -- apply in_map_iff;exists a;auto.
      + apply sub_pom_Boxes in Ib as (Ib&b'&Ib'&Eb').
        assert (IIb' : b' ⊆ map ι ⟪PomType P⟫).
        * rewrite Eb'.
          intros a Ia;apply in_map_iff in Ia as (a'&<-&Ia').
          apply sub_pom_T_internal.
        * apply incl_map in IIb' as (c&->&_).
          assert (I : [map ι c] ≲ Boxes Q)
            by (intros ? [<-|F];[exists (map ι c);split;[assumption|reflexivity]
                                  |exfalso;apply F]).
          apply Embedding_box in I as (β&Iβ&Eβ);[now left|].
          destruct (sub_pom_invert_boxes _ Iβ (@domain_incl _ _)) as (γ&Iγ&Eγ).
          exists (map f γ);split;[apply in_map_iff;exists γ;tauto|].
          rewrite Eβ,<-Eγ,map_map in Eb'.
          erewrite <- map_ext in Eb' by apply h__f.
          intro a;transitivity (𝒯e a ∈ map (𝒯l {{map ι ⟪ PomType P ⟫}}) b).
          -- split;intros I.
             ++ apply in_map_iff;exists a;auto.
             ++ apply in_map_iff in I as (x&Ex&Ix).
                apply is_injective in Ex as ->;assumption.
          -- rewrite <- Eb';split;intros I;apply in_map_iff in I as (x&Ex&Ix);
               apply in_map_iff.
             ++ apply is_injective in Ex as <-.
                exists x;tauto.
             ++ subst;exists x;tauto.
  Qed.
  
  Lemma sub_pom_Embedding P l : Embedding (P⇂l) P (𝒯l {{l}}).
  Proof.
    split.
    - typeclasses eauto.
    - intro;reflexivity.
    - intros;reflexivity.
    - intros b;split;intros I ? [<-|F];try (exfalso;apply F).
      + destruct (I b) as (b'&Ib'&Eb');[now left|].
        apply sub_pom_Boxes in Ib' as (Ib'&β&Iβ&Eβ).
        exists β;split;[assumption|].
        rewrite Eb',Eβ;reflexivity.
      + destruct (I (map (𝒯l {{l}}) b)) as (b'&Ib'&Eb');[now left|].
        cut (b' ⊆ l).
        * intros h;apply (sub_pom_invert_boxes _ Ib') in h as (β&Iβ&Eβ).
          exists β;split;[assumption|].
          rewrite <- Eb' in Eβ.
          intro a;transitivity (𝒯e a ∈ (map (𝒯l {{l}}) β));[rewrite Eβ|symmetry];
            (split;[intro;apply in_map_iff;exists a;tauto
                   |intro Ia;apply in_map_iff in Ia as (x&Ex&Ix);
                    apply is_injective in Ex as ->;assumption]).
        * intros a Ia;apply Eb',in_map_iff in Ia as (x&<-&Ix).
          apply sub_pom_T_internal.
  Qed.
  
  Global Instance Embedding_seq_l P Q : Embedding P (P⋅Q) inl.
  Proof.
    split.
    - split;intros x y E;inversion E;reflexivity.
    - intro a;reflexivity.
    - intros a b;reflexivity.
    - intros b;split;intros h ? [<-|F];try (exfalso;apply F).
      + destruct (h b) as (b'&Ib'&Eb');[now left|].
        exists (map inl b');split;[|rewrite Eb';reflexivity].
        apply in_app_iff;left;apply in_map_iff;exists b';tauto.
      + destruct (h (map inl b)) as (b'&Ib'&Eb');[now left|].
        apply in_app_iff in Ib' as [Ib'|Ib'];apply in_map_iff in Ib' as (b''&<-&Ib'').
        * exists b'';split;auto.
          intros a;transitivity (@inl _ ⌊Q⌋ a ∈ map inl b);[symmetry|rewrite Eb'];
            (split;intros I;[apply in_map_iff in I as (x&E&Ix);inversion E;subst;assumption
                            |apply in_map_iff;exists a;tauto]).
        * exfalso.
          destruct b'' as [|e b''];[eapply Pomset_hnil,Ib''|].
          cut (@inr ⌊P⌋ _ e ∈ map inr (e::b''));[|now left].
          rewrite <- Eb';intros F;apply in_map_iff in F as (y&F&_);discriminate.
  Qed.

  Global Instance Embedding_seq_r P Q : Embedding Q (P⋅Q) inr.
  Proof.
    split.
    - split;intros x y E;inversion E;reflexivity.
    - intro a;reflexivity.
    - intros a b;reflexivity.
    - intros b;split;intros h ? [<-|F];try (exfalso;apply F).
      + destruct (h b) as (b'&Ib'&Eb');[now left|].
        exists (map inr b');split;[|rewrite Eb';reflexivity].
        apply in_app_iff;right;apply in_map_iff;exists b';tauto.
      + destruct (h (map inr b)) as (b'&Ib'&Eb');[now left|].
        apply in_app_iff in Ib' as [Ib'|Ib'];apply in_map_iff in Ib' as (b''&<-&Ib'').
        * exfalso.
          destruct b'' as [|e b''];[eapply Pomset_hnil,Ib''|].
          cut (@inl _ ⌊Q⌋ e ∈ map inl (e::b''));[|now left].
          rewrite <- Eb';intros F;apply in_map_iff in F as (y&F&_);discriminate.
        * exists b'';split;auto.
          intros a;transitivity (@inr ⌊P⌋ _ a ∈ map inr b);[symmetry|rewrite Eb'];
            (split;intros I;[apply in_map_iff in I as (x&E&Ix);inversion E;subst;assumption
                            |apply in_map_iff;exists a;tauto]).
  Qed.
  
  Global Instance Embedding_par_l P Q : Embedding P (P∥Q) inl.
  Proof.
    split.
    - split;intros x y E;inversion E;reflexivity.
    - intro a;reflexivity.
    - intros a b;reflexivity.
    - intros b;split;intros h ? [<-|F];try (exfalso;apply F).
      + destruct (h b) as (b'&Ib'&Eb');[now left|].
        exists (map inl b');split;[|rewrite Eb';reflexivity].
        apply in_app_iff;left;apply in_map_iff;exists b';tauto.
      + destruct (h (map inl b)) as (b'&Ib'&Eb');[now left|].
        apply in_app_iff in Ib' as [Ib'|Ib'];apply in_map_iff in Ib' as (b''&<-&Ib'').
        * exists b'';split;auto.
          intros a;transitivity (@inl _ ⌊Q⌋ a ∈ map inl b);[symmetry|rewrite Eb'];
            (split;intros I;[apply in_map_iff in I as (x&E&Ix);inversion E;subst;assumption
                            |apply in_map_iff;exists a;tauto]).
        * exfalso.
          destruct b'' as [|e b''];[eapply Pomset_hnil,Ib''|].
          cut (@inr ⌊P⌋ _ e ∈ map inr (e::b''));[|now left].
          rewrite <- Eb';intros F;apply in_map_iff in F as (y&F&_);discriminate.
  Qed.

  Global Instance Embedding_par_r P Q : Embedding Q (P∥Q) inr.
  Proof.
    split.
    - split;intros x y E;inversion E;reflexivity.
    - intro a;reflexivity.
    - intros a b;reflexivity.
    - intros b;split;intros h ? [<-|F];try (exfalso;apply F).
      + destruct (h b) as (b'&Ib'&Eb');[now left|].
        exists (map inr b');split;[|rewrite Eb';reflexivity].
        apply in_app_iff;right;apply in_map_iff;exists b';tauto.
      + destruct (h (map inr b)) as (b'&Ib'&Eb');[now left|].
        apply in_app_iff in Ib' as [Ib'|Ib'];apply in_map_iff in Ib' as (b''&<-&Ib'').
        * exfalso.
          destruct b'' as [|e b''];[eapply Pomset_hnil,Ib''|].
          cut (@inl _ ⌊Q⌋ e ∈ map inl (e::b''));[|now left].
          rewrite <- Eb';intros F;apply in_map_iff in F as (y&F&_);discriminate.
        * exists b'';split;auto.
          intros a;transitivity (@inr ⌊P⌋ _ a ∈ map inr b);[symmetry|rewrite Eb'];
            (split;intros I;[apply in_map_iff in I as (x&E&Ix);inversion E;subst;assumption
                            |apply in_map_iff;exists a;tauto]).
  Qed.

  Global Instance Embedding_bsp_seq_l s t : Embedding ⟦s⟧ ⟦s⋅t⟧ inl.
  Proof. apply Embedding_seq_l. Qed.
  
  Global Instance Embedding_bsp_seq_r s t : Embedding ⟦t⟧ ⟦s⋅t⟧ inr.
  Proof. apply Embedding_seq_r. Qed.
  
  Global Instance Embedding_bsp_par_l s t : Embedding ⟦s⟧ ⟦s∥t⟧ inl.
  Proof. apply Embedding_par_l. Qed.
  
  Global Instance Embedding_bsp_par_r s t : Embedding ⟦t⟧ ⟦s∥t⟧ inr.
  Proof. apply Embedding_par_r. Qed.
    
  Definition embedded : relation (Pomset X) := fun P Q => exists f, Embedding P Q f.
  
  Infix " ⫇ " := embedded (at level 80).
  
  Global Instance embedded_PreOrder : PreOrder embedded.
  Proof.
    split.
    - intro P;exists id;apply Embedding_id.
    - intros P Q R (f&Ef) (g&Eg);exists (g∘f);apply Embedding_compose;assumption.
  Qed.

  Lemma embedded_partialOrder : PartialOrder sequiv embedded.
  Proof.
    intros P Q;split.
    - intros E;split;[symmetry in E|];destruct E as (f&If);exists f;apply Embedding_iso,If.
    - unfold Basics.flip;intros ((f&Emb__f)&E).
      rewrite <- (sub_pom_full Q);etransitivity;
        [apply Embedding_is_sub_pom,Emb__f|apply sub_pom_proper].
      symmetry;apply domain_equiv.
      cut (⎢ PomType Q ⎥ <= ⎢ PomType P ⎥).
      + intros len;apply NoDup_length_incl.
        * apply NoDup_map_injective,domain_nodup.
          apply Embedding_inj.
        * rewrite map_length;apply len.
        * apply domain_incl.
      + destruct E as (g&Emb__g).
        apply Embedding_is_sub_pom in Emb__g.
        apply sizePomset_equiv in Emb__g;unfold size,sizePomset in Emb__g;rewrite Emb__g.
        unfold sub_pom,𝒯;simpl.
        rewrite bintree_of_nat_size.
        unfold size at 2,size_type.
        apply NoDup_length,NoDup_undup.
        apply domain_incl.
  Qed.

  Lemma embedded_seq_left P Q : P ⫇ P ⋅ Q.
  Proof. eexists;apply Embedding_seq_l. Qed.
  Lemma embedded_seq_right P Q : Q ⫇ P ⋅ Q.
  Proof. eexists;apply Embedding_seq_r. Qed.

  Lemma embedded_par_left P Q : P ⫇ P ∥ Q.
  Proof. eexists;apply Embedding_par_l. Qed.
  Lemma embedded_par_right P Q : Q ⫇ P ∥ Q.
  Proof. eexists;apply Embedding_par_r. Qed.

  Lemma embedded_iff_sub_pom P Q : P ⫇ Q <-> exists l, P ≃ Q ⇂ l.
  Proof.
    split.
    - intros (f&Ef);eexists;apply Embedding_is_sub_pom,Ef.
    - intros (l&E).
      apply embedded_partialOrder in E as (->&_).
      eexists;apply sub_pom_Embedding.
  Qed.

  Lemma embedded_unit P : 𝟭 ⫇ P.
  Proof. apply embedded_iff_sub_pom;exists [];symmetry;apply sub_pom_nil. Qed.


  Fixpoint sub_term t : list ⌊|t|⌋ -> bsp_terms X :=
    match t with
    | bsp_unit =>
      fun _ => bsp_unit
    | bsp_var x =>
      fun l => if l =?= [] then bsp_unit else bsp_var x
    | bsp_seq t1 t2 =>
      fun l => bsp_seq (sub_term t1 (bsp_get_seq_left l))
                    (sub_term t2 (bsp_get_seq_right l))
    | bsp_par t1 t2 =>
      fun l => bsp_par (sub_term t1 (bsp_get_par_left l))
                    (sub_term t2 (bsp_get_par_right l))
    | bsp_box s =>
      fun l => if equivalentb (get_box_boxes l) ⟨|s|⟩
            then bsp_box s
            else sub_term s (get_box_boxes l)
    end.

  Infix " ⨡ " := sub_term (at level 20).
  
  Lemma sub_pom_seq_dec t1 t2 l :
    t1 ⇂ get_seq_left l ⋅ t2 ⇂ get_seq_right l ≃ ( t1 ⋅ t2 ) ⇂ l.
  Proof.
    destruct (@sub_pom_make_fun t1 (t1 ⋅ t2) (get_seq_left l)
                                l inl) as (f1&Ef1);
      [intros a Ia;apply in_map_iff in Ia as (b&<-&Ib);
       apply get_seq_left_spec in Ib;assumption|].
    destruct (@sub_pom_make_fun t2 (t1⋅t2) (get_seq_right l)
                                l inr) as (f2&Ef2);
      [intros a Ia;apply in_map_iff in Ia as (b&<-&Ib);
       apply get_seq_right_spec in Ib;assumption|].
    symmetry.
    exists (sumFun f1 f2);split.
    + split;split.
      * intros x' y';unfold sumFun.
        destruct x' as [x|x],y' as [y|y].
        -- simpl;intros E;f_equal.
           apply (@is_injective _ _ _ (@sub_pom_T_injective _ _)). 
           eapply (@is_injective _ _ _ (@injective_inl _ _)). 
           rewrite <- Ef1,<-Ef1,E;reflexivity.
        -- intros F;exfalso.
           pose proof (Ef1 x) as E.
           rewrite F,Ef2 in E.
           discriminate.
        -- intros F;exfalso.
           pose proof (Ef2 x) as E.
           rewrite F,Ef1 in E.
           discriminate.
        -- intros E;f_equal.
           apply (@is_injective _ _ _ (@sub_pom_T_injective _ _)). 
           eapply (@is_injective _ _ _ (@injective_inr _ _)). 
           rewrite <- Ef2,<-Ef2,E;reflexivity.
      * intro y.
        pose proof (sub_pom_T_internal y) as Iy.
        apply get_seq_seq_proj in Iy.
        apply in_app_iff in Iy as [Iy|Iy];apply in_map_iff in Iy as (x&Ex&Ix);
          simpl.
        -- apply sub_pom_T_invert in Ix as (x'&<-);simpl.
           rewrite <- Ef1 in Ex.
           apply is_injective in Ex as <-.
           exists (inl x');reflexivity.
        -- apply sub_pom_T_invert in Ix as (x'&<-);simpl.
           rewrite <- Ef2 in Ex.
           apply is_injective in Ex as <-.
           exists (inr x');reflexivity.
    + intros [x|x];simpl;rewrite Ef1||rewrite Ef2;reflexivity.
    + intros [x|x] [y|y];simpl;repeat rewrite Ef1||rewrite Ef2;reflexivity.
    + simpl.
      repeat rewrite map_map||rewrite map_app.
      etransitivity;[apply equiv_set_app_Proper;apply eq_subrelation;
                     (typeclasses eauto)||(apply map_ext;apply map_map)|].
      simpl.
      split;intros b' Ib'.
      * apply in_app_iff in Ib' as [Ib|Ib];apply in_map_iff in Ib as (b&<-&Ib);
          apply sub_pom_Boxes in Ib as (Ib&β&Iβ&Eβ).
        -- assert (map inl β ∈ Boxes (t1 ⋅ t2)
                   /\ map inl β ⊆ l) as (Iβ'&h__β);[split|].
           ++ simpl;apply in_app_iff;left;apply in_map_iff;exists β;split;[reflexivity|apply Iβ].
           ++ rewrite Eβ,map_map.
              intros a Ia;apply in_map_iff in Ia as (x&<-&Ix).
              rewrite <- Ef1;apply (sub_pom_T_internal (f1 x)).
           ++ apply (sub_pom_invert_boxes _ Iβ') in h__β as (γ&Iγ&Eγ).
              exists γ;split;[assumption|].
              rewrite Eβ,map_map in Eγ.
              intro a;transitivity (𝒯e a ∈ map (𝒯l {{l}}) γ).
              --- rewrite Eγ;repeat rewrite in_map_iff.
                  split;intros (x&E&Ix);exists x;subst;auto.
                  split;[|assumption].
                  rewrite <- (Ef1 x) in E.
                  apply is_injective in E;assumption.
              --- rewrite in_map_iff;split;[|intro I;exists a;tauto].
                  intros (y&E&Iy).
                  apply is_injective in E as ->;tauto.
        -- assert (map inr β ∈ Boxes (t1⋅t2)
                   /\ map inr β ⊆ l) as (Iβ'&h__β);[split|].
           ++ simpl;apply in_app_iff;right;apply in_map_iff;exists β;split;
                [reflexivity|apply Iβ].
           ++ rewrite Eβ,map_map.
              intros a Ia;apply in_map_iff in Ia as (x&<-&Ix).
              rewrite <- Ef2;apply (sub_pom_T_internal (f2 x)).
           ++ apply (sub_pom_invert_boxes _ Iβ') in h__β as (γ&Iγ&Eγ).
              exists γ;split;[assumption|].
              rewrite Eβ,map_map in Eγ.
              intro a;transitivity (𝒯e a ∈ map (𝒯l {{l}}) γ).
              --- rewrite Eγ;repeat rewrite in_map_iff.
                  split;intros (x&E&Ix);exists x;subst;auto.
                  split;[|assumption].
                  rewrite <- (Ef2 x) in E.
                  apply is_injective in E;assumption.
              --- rewrite in_map_iff;split;[|intro I;exists a;tauto].
                  intros (y&E&Iy).
                  apply is_injective in E as ->;tauto.
      * apply (@sub_pom_box_spec _ l b') in Ib' as (Ib'&β&Iβ&Eβ).
        simpl in Iβ;apply in_app_iff in Iβ as [I|I];apply in_map_iff in I as (γ&<-&Iγ).
        -- assert (γ ⊆ get_seq_left l) as h__γ.
           ++ intros e Ie;apply get_seq_left_spec.
              cut (@inl _ ⌊|t2|⌋ e ∈ map (𝒯l {{l}}) b');[|apply Eβ,in_map_iff;exists e;tauto].
              intros h;apply in_map_iff in h as (x&E&Ix).
              replace (inl _) with (𝒯e x).
              apply (sub_pom_T_internal x).
           ++ apply (sub_pom_invert_boxes _ Iγ) in h__γ as (β&Iβ&Eγ).
              rewrite <- Eγ in Eβ;clear γ Eγ Iγ.
              exists (map f1 β);split.
              ** apply in_app_iff;left.
                 apply in_map_iff;exists β;split;[reflexivity|assumption].
              ** intro a;transitivity (𝒯e a ∈ map (𝒯l {{l}}) b').
                 --- rewrite in_map_iff;split;[intro I;exists a;tauto|].
                     intros (x&E&Ix).
                     apply is_injective in E as ->;tauto.
                 --- rewrite <- Eβ,map_map;split;intro I;apply in_map_iff in I as (x&E&Ix);
                       apply in_map_iff;exists x;split;auto.
                     +++ apply (@is_injective _ _ _ sub_pom_T_injective).
                         rewrite Ef1;apply E.
                     +++ rewrite <- Ef1,E;reflexivity.
        -- assert (γ ⊆ get_seq_right l) as h__γ.
           ++ intros e Ie;apply get_seq_right_spec.
              cut (@inr _ ⌊|t2|⌋ e ∈ map (𝒯l {{l}}) b');[|apply Eβ,in_map_iff;exists e;tauto].
              intros h;apply in_map_iff in h as (x&E&Ix).
              replace (inr _) with (𝒯e x).
              apply (sub_pom_T_internal x).
           ++ apply (sub_pom_invert_boxes _ Iγ) in h__γ as (β&Iβ&Eγ).
              rewrite <- Eγ in Eβ;clear γ Eγ Iγ.
              exists (map f2 β);split.
              ** apply in_app_iff;right.
                 apply in_map_iff;exists β;split;[reflexivity|assumption].
              ** intro a;transitivity (𝒯e a ∈ map (𝒯l {{l}}) b').
                 --- rewrite in_map_iff;split;[intro I;exists a;tauto|].
                     intros (x&E&Ix).
                     apply is_injective in E as ->;tauto.
                 --- rewrite <- Eβ,map_map;split;intro I;apply in_map_iff in I as (x&E&Ix);
                       apply in_map_iff;exists x;split;auto.
                     +++ apply (@is_injective _ _ _ sub_pom_T_injective).
                         rewrite Ef2;apply E.
                     +++ rewrite <- Ef2,E;reflexivity.
  Qed.
  Corollary sub_term_seq_dec t1 t2 l :
    ⟦ t1 ⟧ ⇂ bsp_get_seq_left l ⋅ ⟦ t2 ⟧ ⇂ bsp_get_seq_right l ≃ ⟦ t1 ⋅ t2 ⟧ ⇂ l.
  Proof. apply sub_pom_seq_dec. Qed.
  
  Lemma sub_pom_par_dec t1 t2 l :
     t1 ⇂ get_par_left l ∥ t2 ⇂ get_par_right l ≃ (t1 ∥ t2 ) ⇂ l.
  Proof.
    destruct (@sub_pom_make_fun t1 (t1∥t2) (get_par_left l)
                                l inl) as (f1&Ef1);
      [intros a Ia;apply in_map_iff in Ia as (b&<-&Ib);
       apply get_par_left_spec in Ib;assumption|].
    destruct (@sub_pom_make_fun t2 (t1∥t2) (get_par_right l)
                                l inr) as (f2&Ef2);
      [intros a Ia;apply in_map_iff in Ia as (b&<-&Ib);
       apply get_par_right_spec in Ib;assumption|].
    symmetry.
    exists (sumFun f1 f2);split.
    + split;split.
      * intros x' y';unfold sumFun.
        destruct x' as [x|x],y' as [y|y].
        -- simpl;intros E;f_equal.
           apply (@is_injective _ _ _ (@sub_pom_T_injective _ _)). 
           eapply (@is_injective _ _ _ (@injective_inl _ _)). 
           rewrite <- Ef1,<-Ef1,E;reflexivity.
        -- intros F;exfalso.
           pose proof (Ef1 x) as E.
           rewrite F,Ef2 in E.
           discriminate.
        -- intros F;exfalso.
           pose proof (Ef2 x) as E.
           rewrite F,Ef1 in E.
           discriminate.
        -- intros E;f_equal.
           apply (@is_injective _ _ _ (@sub_pom_T_injective _ _)). 
           eapply (@is_injective _ _ _ (@injective_inr _ _)). 
           rewrite <- Ef2,<-Ef2,E;reflexivity.
      * intro y.
        pose proof (sub_pom_T_internal y) as Iy.
        apply get_par_par_proj in Iy.
        apply in_app_iff in Iy as [Iy|Iy];apply in_map_iff in Iy as (x&Ex&Ix);
          simpl.
        -- apply sub_pom_T_invert in Ix as (x'&<-);simpl.
           rewrite <- Ef1 in Ex.
           apply is_injective in Ex as <-.
           exists (inl x');reflexivity.
        -- apply sub_pom_T_invert in Ix as (x'&<-);simpl.
           rewrite <- Ef2 in Ex.
           apply is_injective in Ex as <-.
           exists (inr x');reflexivity.
    + intros [x|x];simpl;rewrite Ef1||rewrite Ef2;reflexivity.
    + intros [x|x] [y|y];simpl;repeat rewrite Ef1||rewrite Ef2;reflexivity.
    + simpl.
      repeat rewrite map_map||rewrite map_app.
      etransitivity;[apply equiv_set_app_Proper;apply eq_subrelation;
                     (typeclasses eauto)||(apply map_ext;apply map_map)|].
      simpl.
      split;intros b' Ib'.
      * apply in_app_iff in Ib' as [Ib|Ib];apply in_map_iff in Ib as (b&<-&Ib);
          apply sub_pom_Boxes in Ib as (Ib&β&Iβ&Eβ).
        -- assert (map inl β ∈ Boxes (t1∥t2)
                   /\ map inl β ⊆ l) as (Iβ'&h__β);[split|].
           ++ simpl;apply in_app_iff;left;apply in_map_iff;exists β;split;[reflexivity|apply Iβ].
           ++ rewrite Eβ,map_map.
              intros a Ia;apply in_map_iff in Ia as (x&<-&Ix).
              rewrite <- Ef1;apply (sub_pom_T_internal (f1 x)).
           ++ apply (sub_pom_invert_boxes _ Iβ') in h__β as (γ&Iγ&Eγ).
              exists γ;split;[assumption|].
              rewrite Eβ,map_map in Eγ.
              intro a;transitivity (𝒯e a ∈ map (𝒯l {{l}}) γ).
              --- rewrite Eγ;repeat rewrite in_map_iff.
                  split;intros (x&E&Ix);exists x;subst;auto.
                  split;[|assumption].
                  rewrite <- (Ef1 x) in E.
                  apply is_injective in E;assumption.
              --- rewrite in_map_iff;split;[|intro I;exists a;tauto].
                  intros (y&E&Iy).
                  apply is_injective in E as ->;tauto.
        -- assert (map inr β ∈ Boxes (t1∥t2)
                   /\ map inr β ⊆ l) as (Iβ'&h__β);[split|].
           ++ simpl;apply in_app_iff;right;apply in_map_iff;exists β;split;
                [reflexivity|apply Iβ].
           ++ rewrite Eβ,map_map.
              intros a Ia;apply in_map_iff in Ia as (x&<-&Ix).
              rewrite <- Ef2;apply (sub_pom_T_internal (f2 x)).
           ++ apply (sub_pom_invert_boxes _ Iβ') in h__β as (γ&Iγ&Eγ).
              exists γ;split;[assumption|].
              rewrite Eβ,map_map in Eγ.
              intro a;transitivity (𝒯e a ∈ map (𝒯l {{l}}) γ).
              --- rewrite Eγ;repeat rewrite in_map_iff.
                  split;intros (x&E&Ix);exists x;subst;auto.
                  split;[|assumption].
                  rewrite <- (Ef2 x) in E.
                  apply is_injective in E;assumption.
              --- rewrite in_map_iff;split;[|intro I;exists a;tauto].
                  intros (y&E&Iy).
                  apply is_injective in E as ->;tauto.
      * apply (@sub_pom_box_spec _ l b') in Ib' as (Ib'&β&Iβ&Eβ).
        simpl in Iβ;apply in_app_iff in Iβ as [I|I];apply in_map_iff in I as (γ&<-&Iγ).
        -- assert (γ ⊆ get_par_left l) as h__γ.
           ++ intros e Ie;apply get_par_left_spec.
              cut (@inl _ ⌊|t2|⌋ e ∈ map (𝒯l {{l}}) b');[|apply Eβ,in_map_iff;exists e;tauto].
              intros h;apply in_map_iff in h as (x&E&Ix).
              replace (inl _) with (𝒯e x).
              apply (sub_pom_T_internal x).
           ++ apply (sub_pom_invert_boxes _ Iγ) in h__γ as (β&Iβ&Eγ).
              rewrite <- Eγ in Eβ;clear γ Eγ Iγ.
              exists (map f1 β);split.
              ** apply in_app_iff;left.
                 apply in_map_iff;exists β;split;[reflexivity|assumption].
              ** intro a;transitivity (𝒯e a ∈ map (𝒯l {{l}}) b').
                 --- rewrite in_map_iff;split;[intro I;exists a;tauto|].
                     intros (x&E&Ix).
                     apply is_injective in E as ->;tauto.
                 --- rewrite <- Eβ,map_map;split;intro I;apply in_map_iff in I as (x&E&Ix);
                       apply in_map_iff;exists x;split;auto.
                     +++ apply (@is_injective _ _ _ sub_pom_T_injective).
                         rewrite Ef1;apply E.
                     +++ rewrite <- Ef1,E;reflexivity.
        -- assert (γ ⊆ get_par_right l) as h__γ.
           ++ intros e Ie;apply get_par_right_spec.
              cut (@inr _ ⌊|t2|⌋ e ∈ map (𝒯l {{l}}) b');[|apply Eβ,in_map_iff;exists e;tauto].
              intros h;apply in_map_iff in h as (x&E&Ix).
              replace (inr _) with (𝒯e x).
              apply (sub_pom_T_internal x).
           ++ apply (sub_pom_invert_boxes _ Iγ) in h__γ as (β&Iβ&Eγ).
              rewrite <- Eγ in Eβ;clear γ Eγ Iγ.
              exists (map f2 β);split.
              ** apply in_app_iff;right.
                 apply in_map_iff;exists β;split;[reflexivity|assumption].
              ** intro a;transitivity (𝒯e a ∈ map (𝒯l {{l}}) b').
                 --- rewrite in_map_iff;split;[intro I;exists a;tauto|].
                     intros (x&E&Ix).
                     apply is_injective in E as ->;tauto.
                 --- rewrite <- Eβ,map_map;split;intro I;apply in_map_iff in I as (x&E&Ix);
                       apply in_map_iff;exists x;split;auto.
                     +++ apply (@is_injective _ _ _ sub_pom_T_injective).
                         rewrite Ef2;apply E.
                     +++ rewrite <- Ef2,E;reflexivity.
  Qed.
  Corollary sub_term_par_dec t1 t2 l :
    ⟦ t1 ⟧ ⇂ bsp_get_par_left l ∥ ⟦ t2 ⟧ ⇂ bsp_get_par_right l ≃ ⟦ t1 ∥ t2 ⟧ ⇂ l.
  Proof. apply sub_pom_par_dec. Qed.
    
  Lemma sub_term_sub_pom t l : ⟦t ⨡ l⟧ ≃ ⟦t⟧⇂l.
  Proof.
    revert l;induction t;intro l;rsimpl.
    - rewrite IHt1,IHt2,sub_term_seq_dec;reflexivity.
    - rewrite IHt1,IHt2,sub_term_par_dec;reflexivity.
    - destruct l as [|[]];simpl.
      + rewrite eqX_refl, sub_pom_nil;reflexivity.
      + replace (_=?=_) with false by (symmetry;apply eqX_false;discriminate).
        symmetry;etransitivity;[|apply sub_pom_full].
        apply sub_pom_proper.
        symmetry;apply domain_equiv.
        intros [] _;now left.
    - case_eq (equivalentb (get_box_boxes l) ⟨|t|⟩);
        [|rewrite <-not_true_iff_false];rewrite equivalentb_spec;intros El.
      + symmetry;etransitivity;[|apply sub_pom_full];rsimpl.
        apply sub_pom_proper.
        apply El.
      + rewrite IHt.
        clear IHt.
        assert (exists e, ~ e ∈ (get_box_boxes l)) as (e&Ie)
            by (case_prop (exists e, ~ e ∈ (get_box_boxes l));auto;exfalso;apply El,antisymmetry;
                [apply domain_incl
                |intros f _;case_in f (get_box_boxes l);auto;exfalso;apply hyp;exists f;tauto]).
        clear El.
        revert l e Ie.
        unfold interpret,get_box_boxes,id;simpl.
        generalize (sem_bsp t);clear t;simpl.
        intros p l e Ie.
        exists id;split.
        * typeclasses eauto.
        * reflexivity.
        * reflexivity.
        * apply equivalent_equiv_sets;intro.
          destruct (Boxes_box_spec p) as [F|E].
          -- exfalso.
             symmetry in F;destruct F as (f&_).
             pose proof (domain_spec (f e)) as Ie'.
             apply Ie'.
          -- split.
             ++ intros I;apply in_map_iff in I as (y&<-&Iy).
                apply sub_pom_Boxes in Iy as (Iy&β&Iβ&Eβ).
                rewrite E in Iβ;destruct Iβ as [<-|Iβ].
                ** exfalso;apply Ie.
                   cut (e ∈ ⟪PomType p⟫);[|apply domain_spec].
                   rewrite Eβ;intro I;apply in_map_iff in I as (e'&<-&I).
                   apply (@sub_pom_T_internal p l e').
                ** apply sub_pom_Boxes;rewrite map_id;split;[apply Iy|].
                   exists β;split;assumption.
             ++ intro I;apply in_map_iff;exists x;split;[apply map_id|].
                apply sub_pom_Boxes in I as (Ix&y&Iy&Ey).
                apply sub_pom_Boxes;split;[assumption|].
                exists y;split;[|assumption].
                rewrite E;now right.
    - symmetry;etransitivity;[|apply sub_pom_nil].
      apply sub_pom_proper.
      destruct l as [|[]];reflexivity.
  Qed.

  Lemma sub_term_nil s : sub_term s [] ≡ 𝟭.
  Proof.
    apply bsp_size_unit.
    rewrite interpret_bsp_size.
    rewrite (sizePomset_equiv (sub_term_sub_pom _ _)).
    unfold size,sizePomset,sub_pom;simpl.
    reflexivity.
  Qed.


  Global Instance sub_term_proper s : Proper (@equivalent _ ==> eq) (sub_term s).
  Proof.
    induction s;intros l m E;simpl.
    - pose proof E as E'.
      apply bsp_get_seq_left_proper in E as ->.
      apply bsp_get_seq_right_proper in E' as ->.
      reflexivity.
    - pose proof E as E'.
      apply bsp_get_par_left_proper in E as ->.
      apply bsp_get_par_right_proper in E' as ->.
      reflexivity.
    - destruct l as [|a l],m as [|b m].
      + reflexivity.
      + exfalso;cut (b ∈ (b::m));[intro I;apply E in I;apply I|now left].
      + exfalso;cut (a ∈ (a::l));[intro I;apply E in I;apply I|now left].
      + repeat replace (_ =?= _) with false by (symmetry;apply eqX_false;discriminate).
        reflexivity.
    - replace (equivalentb (get_box_boxes l) ⟨|s|⟩)
        with (equivalentb (get_box_boxes m) ⟨|s|⟩).
      + destruct (equivalentb (get_box_boxes m) ⟨|s|⟩);[|rewrite E];reflexivity.
      + apply eq_true_iff_eq.
        repeat rewrite equivalentb_spec.
        rewrite E;reflexivity.
    - reflexivity.
  Qed.

  Lemma sub_term_full s : s ⨡⟨|s|⟩ = s.
  Proof.
    induction s;simpl.
    - f_equal;(erewrite sub_term_proper;[eassumption|]).
      + symmetry;apply domain_equiv.
        intros a _;apply get_seq_left_spec,in_app_iff;left.
        apply in_map_iff;exists a;split;[reflexivity|apply domain_spec].
      + symmetry;apply domain_equiv.
        intros a _;apply get_seq_right_spec,in_app_iff;right.
        apply in_map_iff;exists a;split;[reflexivity|apply domain_spec].
    - f_equal;(erewrite sub_term_proper;[eassumption|]).
      + symmetry;apply domain_equiv.
        intros a _;apply get_seq_left_spec,in_app_iff;left.
        apply in_map_iff;exists a;split;[reflexivity|apply domain_spec].
      + symmetry;apply domain_equiv.
        intros a _;apply get_seq_right_spec,in_app_iff;right.
        apply in_map_iff;exists a;split;[reflexivity|apply domain_spec].
    - replace (_ =?= _) with false by (symmetry;apply eqX_false;discriminate).
      reflexivity.
    - replace (get_box_boxes ⟨|bsp_box s|⟩)
        with ⟨|s|⟩.
      + replace (equivalentb _ _) with true;[reflexivity|].
        symmetry;apply equivalentb_spec;reflexivity.
      + clear.
        unfold get_box_boxes,interpret;simpl.
        destruct (sem_bsp s);simpl;reflexivity.
    - reflexivity.
  Qed.



End s.
Arguments sub_pom : clear implicits.
Arguments sub_pom {X} P D.
Infix " ⇂ " := sub_pom (at level 20).
Infix " ⫇ " := embedded (at level 80).
Infix " ⨡ " := sub_term (at level 20).

Arguments sub_pom_box : clear implicits.
