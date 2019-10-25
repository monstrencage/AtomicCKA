Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools algebra Bool relations.
Require Export finite_types notations.


Section order.
  
  Class partialOrder {A} (O : relation ⟨A⟩) :=
    {po_refl :> Reflexive O;
     po_trans :> Transitive O;
     po_anti :> Antisymmetric ⟨A⟩ Logic.eq O;
    }.

  Class decOrder {A} (O : relation ⟨A⟩) :=
    po_dec :> forall x y, DecidableProp (O x y).
    
  Ltac case_order x y :=
    let h := fresh "I" in
    destruct (po_dec x y) as [I|I].
  
  Definition Oϒ : relation ⟨𝟣⟩ := 𝟭.

  Global Instance Oϒ_partialOrder : partialOrder Oϒ.
  Proof.
    repeat split.
    - intros [] [] [];tauto.
    - intros [] [];tauto.
  Qed.

  Global Instance Oϒ_decOrder : decOrder Oϒ.
  Proof. intros [] [];simpl;left;reflexivity. Qed.
  
  Definition sumOrder {A B} (Oa : relation ⟨A⟩) (Ob : relation ⟨B⟩) : relation ⟨A ⊎ B⟩
    := fun x y =>
         match x,y with
         | inl a,inl b => Oa a b
         | inr a,inr b => Ob a b
         | _,_ => False
         end.
  Infix " ⊔ " := sumOrder (at level 40).

  Global Instance sumOrder_partialOrder {A B} (Oa : relation ⟨A⟩) (Ob : relation ⟨B⟩) :
    partialOrder Oa -> partialOrder Ob -> partialOrder (Oa ⊔ Ob).
  Proof.
    intros pa pb;repeat split.
    - intros [];simpl;reflexivity.
    - intros [] [] [];simpl;try tauto||apply pa||apply pb.
    - intros [] [];simpl;try tauto.
      + intros;f_equal;apply antisymmetry;assumption.
      + intros;f_equal;apply antisymmetry;assumption.
  Qed.

  Global Instance sumOrder_decOrder {A B} (Oa : relation ⟨A⟩) (Ob : relation ⟨B⟩) :
    decOrder Oa -> decOrder Ob -> decOrder (Oa ⊔ Ob).
  Proof.
    intros pa pb [a|b] [a'|b'];simpl.
    - case_order a a';[left|right];assumption.
    - right;intro F;apply F.
    - right;intro F;apply F.
    - case_order b b';[left|right];assumption.
  Qed.

  Definition seqOrder {A B} (Oa : relation ⟨A⟩) (Ob : relation ⟨B⟩) : relation ⟨A ⊎ B⟩
    := fun x y =>
         match x,y with
         | inl a,inl b => Oa a b
         | inr a,inr b => Ob a b
         | inl a,inr b => True
         | _,_ => False
         end.
  Infix " ⨾ " := seqOrder (at level 40).
  
  Global Instance seqOrder_partialOrder {A B} (Oa : relation ⟨A⟩) (Ob : relation ⟨B⟩) :
    partialOrder Oa -> partialOrder Ob -> partialOrder (Oa ⨾ Ob).
  Proof.
    intros pa pb;repeat split.
    - intros [];simpl;reflexivity.
    - intros [] [] [];simpl;try tauto||apply pa||apply pb.
    - intros [] [];simpl;try tauto.
      + intros;f_equal;apply antisymmetry;assumption.
      + intros;f_equal;apply antisymmetry;assumption.
  Qed.
  Global Instance seqOrder_decOrder {A B} (Oa : relation ⟨A⟩) (Ob : relation ⟨B⟩) :
    decOrder Oa -> decOrder Ob -> decOrder (Oa ⨾ Ob).
  Proof.
    intros pa pb [a|b] [a'|b'];simpl.
    - case_order a a';[left|right];assumption.
    - left;tauto.
    - right;intro F;apply F.
    - case_order b b';[left|right];assumption.
  Qed.

End order.

Section pomsetdef.
  Context {X : Set}.
  
  Record Pomset : Type :=
    { PomType : bintree ;
      ℓ : type PomType -> X;
      PomOrd : relation (type PomType);
      Boxes : list (list (type PomType));
      Pomset_po :> partialOrder PomOrd;
      Pomset_hnil :> ~ [] ∈ Boxes
    }.

  Notation " ⌊ P ⌋ " := ⟨PomType P⟩.

  Lemma witness_box P b : b ∈ Boxes P -> exists e, e ∈ b.
  Proof. destruct b as [|e];[intro F;exfalso;eapply Pomset_hnil,F|exists e;now left]. Qed.

  Infix " ≤[ P ] " := (@PomOrd P) (at level 80).

  Definition strictOrd (P : Pomset) : relation ⌊P⌋ :=
    fun x y => x ≤[P] y /\ x <> y.
  
  Arguments strictOrd : clear implicits.
  Infix " <[ P ] " := (strictOrd P) (at level 80).
  
  Global Instance partialOrderPomset (P : Pomset) :
    partialOrder (fun a b => a ≤[P] b)
    := (Pomset_po P).

  Global Instance StrictOrderPomset (P : Pomset) :
    StrictOrder (fun a b => a <[P] b).
  Proof.
    split.
    - intros a (_&N);apply N;reflexivity.
    - intros a b c (h1&_) (h2&N);split;[etransitivity;eassumption|].
      intros ->;apply N,antisymmetry;assumption.
  Qed.
  
  Class isomorphism (P Q : Pomset) (ϕ : ⌊P⌋ -> ⌊Q⌋) :=
    {
      iso_bij :> bijective ϕ;
      iso_Lbl :> forall a, ℓ (ϕ a) = ℓ a;
      iso_Ord :> forall a a', a ≤[P] a' <-> ϕ a ≤[Q] ϕ a';
      iso_Boxes :> map (map ϕ) (Boxes P) ≃ Boxes Q
    }.

  Class homomorphism (P Q : Pomset) (ϕ : ⌊P⌋ -> ⌊Q⌋):= 
    {
      hom_bij :> bijective ϕ;
      hom_Lbl :> forall a, ℓ (ϕ a) = ℓ a;
      hom_Ord :> forall a a', a ≤[P] a' -> ϕ a ≤[Q] ϕ a';
      hom_Boxes :> map (map ϕ) (Boxes P) ≲ Boxes Q
    }.

  Global Instance homomorphism_proper (P Q : Pomset) :
    Proper (sequiv ==> iff) (@homomorphism P Q).
  Proof.
    cut (forall P Q,Proper (sequiv ==> Basics.impl) (@homomorphism P Q));
      [intros h f g E;split;apply h;[|symmetry];apply E|clear P Q].
    intros p q f g E H;split.
    - rewrite <- E;apply H.
    - intro;rewrite <- E;apply H.
    - intros ? ?;repeat rewrite <- E;apply H.
    - erewrite map_ext;[apply H|].
      apply map_ext;intro;symmetry;apply E.
  Qed.

  Global Instance isomorphism_proper (P Q : Pomset) :
    Proper (sequiv ==> iff) (@isomorphism P Q).
  Proof.
    cut (forall P Q,Proper (sequiv ==> Basics.impl) (@isomorphism P Q));
      [intros h f g E;split;apply h;[|symmetry];apply E|clear P Q].
    intros p q f g E H;split.
    - rewrite <- E;apply H.
    - intro;rewrite <- E;apply H.
    - intros ? ?;repeat rewrite <- E;apply H.
    - erewrite map_ext;[apply H|].
      apply map_ext;intro;symmetry;apply E.
  Qed.
  
  Global Instance Pomset_equiv : SemEquiv Pomset :=
    fun P Q => exists (ϕ : ⌊Q⌋ -> ⌊P⌋) , isomorphism ϕ.
  Global Instance Pomset_subsumption : Subsumption :=
    fun P Q => exists ϕ: ⌊Q⌋ -> ⌊P⌋ , homomorphism ϕ.
            

  Global Instance id_isomorphism A : isomorphism (@id ⌊A⌋).
  Proof.
    split.
    - apply bijective_inverse_iff; exists id;split;reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite (map_ext _ _ (@map_id _)).
      rewrite map_id;reflexivity.
  Qed.

  Global Instance compose_isomorphism A B C (ϕ : ⌊A⌋ -> ⌊B⌋) (ψ : ⌊B⌋ -> ⌊C⌋) :
    isomorphism ϕ -> isomorphism ψ -> isomorphism (ψ∘ϕ).
  Proof.
    intros I1 I2;split.
    - apply bijective_compose;typeclasses eauto.
    - intros a;unfold Basics.compose.
      rewrite iso_Lbl,iso_Lbl;reflexivity.
    - intros a a';rewrite iso_Ord,iso_Ord;reflexivity.
    - unfold Basics.compose.
      erewrite <- map_ext by apply map_map.
      rewrite <- map_map,iso_Boxes,iso_Boxes.
      reflexivity.
  Qed.

  Global Instance inverse_isomorphism A B ϕ `{isomorphism A B ϕ} : isomorphism (ϕ ̃).
  Proof.
    split.
    - apply bijective_inverse_iff;exists ϕ;split;[apply inverse_elim2|apply inverse_elim1].
    - intro a.
      rewrite <- (@inverse_elim2 _ _ ϕ _ a) at 2.
      rewrite <- iso_Lbl;reflexivity.
    - intros a a';rewrite (@iso_Ord _ _ ϕ _).
      rewrite (inverse_elim2 a),inverse_elim2;reflexivity.
    - rewrite <- iso_Boxes,map_map.
      erewrite map_ext;[rewrite map_id;reflexivity|].
      intros a;rewrite map_map.
      erewrite map_ext;[rewrite map_id;reflexivity|].
      apply inverse_elim1.
  Qed.

  Global Instance isomorphism_is_homomorphism P Q (ϕ : ⌊P⌋ -> ⌊Q⌋) :
    isomorphism ϕ -> homomorphism ϕ.
  Proof.
    intros I;split.
    - apply iso_bij.
    - apply iso_Lbl.
    - apply iso_Ord.
    - apply iso_Boxes.
  Qed.

  Global Instance compose_homomorphism A B C (ϕ : ⌊A⌋ -> ⌊B⌋) (ψ : ⌊B⌋ -> ⌊C⌋) :
    homomorphism ϕ -> homomorphism ψ -> homomorphism (ψ∘ϕ).
  Proof.
    intros I1 I2;split.
    - apply bijective_compose;typeclasses eauto.
    - intros a;unfold Basics.compose.
      rewrite hom_Lbl,hom_Lbl;reflexivity.
    - intros a a'.
      intros h;apply hom_Ord,hom_Ord in h.
      apply h.
    - unfold Basics.compose.
      erewrite <- map_ext by apply map_map.
      rewrite <- map_map,hom_Boxes,hom_Boxes.
      reflexivity.
  Qed.

  Global Instance Pomset_equiv_Equivalence : Equivalence sequiv.
  Proof.
    split.
    - intro P;exists id;typeclasses eauto.
    - intros A B (ϕ&Iso);eexists;apply inverse_isomorphism.
    - intros A B C (ϕ&I1) (ϕ'&I2). 
      exists (ϕ∘ϕ');typeclasses eauto.
  Qed.

  Global Instance Pomset_smaller_PreOrder : PreOrder (fun a b => a ⊑ b).
  Proof.
    split.
    - intros p ;exists id;typeclasses eauto.
    - intros A B C (ϕ&h) (ϕ'&h');exists (ϕ∘ϕ');typeclasses eauto. 
  Qed.
    
  Lemma Pomset_bij_subs_iso P Q (ϕ : ⌊P⌋ -> ⌊Q⌋) :
    homomorphism ϕ -> P ⊑ Q -> isomorphism ϕ.
  Proof.
    intros Hom (ϕ'&Hom').
    split;try apply Hom.
    - intros a a';split;[apply hom_Ord|revert a a'].
      set (Φ := ϕ'∘ϕ).
      destruct (@exists_uniform_fixpoint _ Φ) as (ω&hω);
        [apply injective_compose;apply Hom||apply Hom'|].
      intros a a' I.
      cut (forall n, iter_fun Φ (S n) a ≤[P] iter_fun Φ (S n) a').
      + intro h;rewrite <- (hω a),<-(hω a');apply h.
      + intro n;induction n;simpl.
        * repeat rewrite compose_id_r.
          unfold Φ,Basics.compose.
          apply hom_Ord,I.
        * unfold Φ at 1 4,Basics.compose at 2 1 4 5.
          apply hom_Ord,hom_Ord,IHn.
    - split;[apply Hom|].
      destruct (@incl_set_pred_make_function _ _ (undupEq (Boxes Q)) (undupEq (Boxes Q))
                                             (ϕ∘ϕ')) as (θ&hθb&Inj__θ).
      + apply injective_compose;apply Hom||apply Hom'.
      + apply undupEq_NoDupEq.
      + rewrite <- undupEq_eq.
        rewrite <- hom_Boxes at 2.
        unfold Basics.compose.
        erewrite <- map_ext by apply map_map.
        rewrite <- map_map,hom_Boxes;reflexivity.
      + destruct (@exists_uniform_fixpoint _ θ) as (ω&hω).
        * apply Inj__θ.
        * rewrite <- (@hom_Boxes _ _ _ Hom'),map_map.
          intros β Iβ.
          apply undupEq_eq in Iβ as (β'&Iβ&Eβ).
          setoid_rewrite Eβ.
          pose proof (translation_total Iβ) as (b&<-).
          pose proof (hω b) as E.
          apply endofunction_injective_iff_bijective in Inj__θ.
          destruct (is_surjective b) as (α&<-).
          setoid_rewrite <- hθb.
          exists (map (ϕ ∘ ϕ') (𝒯e α));split;[|reflexivity].
          apply in_map_iff;exists (𝒯e α).
          rewrite map_map;split;[reflexivity|].
          apply undupEq_spec.
          apply translation_internal.
  Qed.
    
  Global Instance Pomset_smaller_PartialOrder : PartialOrder sequiv (fun a b => a ⊑ b).
  Proof.
    intros p q;split;unfold Basics.flip.
    - intros E;split.
      + destruct E as (f&E);exists f;typeclasses eauto.
      + symmetry in E; destruct E as (f&E);exists f;typeclasses eauto.
    - intros ((ϕ&hϕ)&E).
      pose proof (Pomset_bij_subs_iso hϕ E) as I;clear hϕ.
      exists ϕ;assumption.
  Qed.
  
  Definition sumFun {s t} (f : ⟨s⟩ -> X) (g : ⟨t⟩ -> X) : ⟨s ⊎ t⟩ -> X :=
    fun x => match x with
          | inl a => f a
          | inr b => g b
          end.
  
  Global Instance sumPomsets : ParProduct Pomset.
  Proof.
    intros P Q.
    apply (@Build_Pomset (PomType P ⊎ PomType Q)
                         (sumFun (@ℓ P) (@ℓ Q))
                         (sumOrder (@PomOrd P) (@PomOrd Q))
                         (map (map inl) (Boxes P) ++ (map (map inr) (Boxes Q)))).
    - typeclasses eauto.
    - rewrite in_app_iff.
      intros [I|I];(apply in_map_iff in I as ([|l]&E&I);[|discriminate]);
        eapply Pomset_hnil,I.
  Defined.

  Global Instance seqPomsets : Product Pomset.
  Proof.
    intros P Q.
    apply (@Build_Pomset (PomType P ⊎ PomType Q)
                         (sumFun (@ℓ P) (@ℓ Q))
                         (seqOrder (@PomOrd P) (@PomOrd Q))
                         (map (map inl) (Boxes P) ++ (map (map inr) (Boxes Q)))).
    - typeclasses eauto.
    - rewrite in_app_iff.
      intros [I|I];(apply in_map_iff in I as ([|l]&E&I);[|discriminate]);
        eapply Pomset_hnil,I.
  Defined.

  Global Instance boxPomsets : Box Pomset.
  Proof.
    intro P.
    apply (@Build_Pomset (PomType P)
                         (@ℓ P)
                         (@PomOrd P)
                         (match ⟪PomType P⟫ with
                          | [] => []
                          | _ => ⟪PomType P⟫::Boxes P
                          end)).
    - typeclasses eauto.
    - destruct ⟪PomType P⟫.
      + intro I;apply I.
      + intros [E|I].
        * discriminate.
        * eapply Pomset_hnil,I.
  Defined.
      
  Global Instance unPomsets : Un Pomset.
  Proof.
    apply (@Build_Pomset _ (fun a : ⟨𝟢⟩ => match a with end) (fun _ _ => False) []).  
    - repeat split;intro;simpl;tauto.
    - simpl;tauto.
  Defined.

  Definition AtomicPomset (x : X) : Pomset :=
    (Build_Pomset (fun a : ⟨𝟣⟩ => x) Oϒ_partialOrder (@in_nil _ _)).  
  
  (* Lemma seq_type p q : (⌊ p ⋅ q ⌋ = ⌊ p ⌋ + ⌊ q ⌋)%type. *)
  (* Proof. *)
  (*   unfold prod,seqPomsets;destruct p as [ t l R po ],q as [ t' l' R' po' ]. *)
  (*   simpl;reflexivity. *)
  (* Qed. *)

  Definition join_fun a b c d (f : ⟨a⟩ -> ⟨b⟩) (g : ⟨c⟩ -> ⟨d⟩) : ⟨a ⊎ c⟩ -> ⟨b ⊎ d⟩ :=
    fun x => match x with
          | inl a => inl (f a)
          | inr c => inr (g c)
          end.
  Infix " ⨝ " := join_fun (at level 40).
  
  Global Instance join_fun_proper a b c d :
    Proper (sequiv ==> sequiv ==> sequiv) (@join_fun a b c d).
  Proof. intros f f' Ef g g' Eg [x|x];simpl;rewrite Ef||rewrite Eg;reflexivity. Qed.

  Global Instance join_fun_inj a b c d  (f : ⟨a⟩ -> ⟨b⟩) (g : ⟨c⟩ -> ⟨d⟩) :
    injective f -> injective g -> injective (f ⨝ g).
  Proof.
    intros h1 h2;split;intros [x|x] [y|y];simpl;intro E;inversion E as [E'];
      apply is_injective in E';subst;reflexivity.
  Qed.
  Global Instance join_fun_surj a b c d  (f : ⟨a⟩ -> ⟨b⟩) (g : ⟨c⟩ -> ⟨d⟩) :
    surjective f -> surjective g -> surjective (f ⨝ g).
  Proof.
    intros h1 h2;split;intros [y|y];destruct (is_surjective y) as (x&<-).
    - exists (inl x);reflexivity.
    - exists (inr x);reflexivity.
  Qed.
  
  Global Instance join_fun_bij a b c d  (f : ⟨a⟩ -> ⟨b⟩) (g : ⟨c⟩ -> ⟨d⟩) :
    bijective f -> bijective g -> bijective (f ⨝ g).
  Proof. intros h1 h2;split;typeclasses eauto. Qed.

  Lemma join_fun_inverse a b c d f g `{bijective ⟨a⟩ ⟨b⟩ f ,bijective ⟨c⟩ ⟨d⟩ g} :
    (f⨝g)̃ ≃ (f ̃⨝g ̃).
  Proof.
    symmetry;apply inverse_unique;intros [x|x];unfold Basics.compose,id;simpl;
      f_equal;apply inverse_elim1||apply inverse_elim2.
  Qed.
    
  Lemma join_fun_inj_iff a b c d  (f : ⟨a⟩ -> ⟨b⟩) (g : ⟨c⟩ -> ⟨d⟩) :
    injective f /\ injective g <-> injective (f ⨝ g).
  Proof.
    split;[intros (h1&h2);typeclasses eauto|].
    intros Inj;split;split.
    - intros x y I.
      cut (@inl _ ⟨c⟩ x = inl y);[intro E;inversion E;reflexivity|].
      apply is_injective;simpl;rewrite I;reflexivity.
    - intros x y I.
      cut (@inr ⟨a⟩ _ x = inr y);[intro E;inversion E;reflexivity|].
      apply is_injective;simpl;rewrite I;reflexivity.
  Qed.
  
  Lemma join_fun_surj_iff a b c d  (f : ⟨a⟩ -> ⟨b⟩) (g : ⟨c⟩ -> ⟨d⟩) :
    surjective f /\ surjective g <-> surjective (f ⨝ g).
  Proof.
    split;[intros (h1&h2);typeclasses eauto|].
    intro Surj;split;split;intros y.
    - destruct (is_surjective (@inl _ ⟨d⟩ y)) as ([x|x]&E);inversion E;subst;
        exists x;reflexivity.
    - destruct (is_surjective (@inr ⟨b⟩ _ y)) as ([x|x]&E);inversion E;subst;
        exists x;reflexivity.
  Qed.
  
  Lemma join_fun_bij_iff a b c d  (f : ⟨a⟩ -> ⟨b⟩) (g : ⟨c⟩ -> ⟨d⟩) :
    bijective f /\ bijective g <-> bijective (f ⨝ g).
  Proof.
    split;[intros (h1&h2);typeclasses eauto|].
    intros (h1&h2);apply join_fun_inj_iff in h1;apply join_fun_surj_iff in h2.
    split;split;tauto.
  Qed.

  Global Instance hom_par p q r s f g :
    @homomorphism p q f -> @homomorphism r s g -> @homomorphism (p∥r) (q∥s) (f ⨝ g).
  Proof.
    intros Hf Hg;split.
    - typeclasses eauto.
    - intros [];simpl;apply hom_Lbl.
    - intros [x|x] [y|y];simpl;apply hom_Ord||tauto.
    - simpl.
      repeat rewrite map_map||rewrite map_app.
      erewrite map_ext by apply map_map.
      erewrite (map_ext (fun x : list ⟨ PomType r ⟩ => map (f ⨝ g) (map inr x)))
        by apply map_map.
      apply smaller_set_app_Proper.
      + rewrite <- (@hom_Boxes _ _ _ Hf),map_map.
        erewrite (map_ext (fun x : list ⌊p⌋ => map inl (map f x)))
          by apply map_map.
        reflexivity.
      + rewrite <- (@hom_Boxes _ _ _ Hg),map_map.
        erewrite (map_ext (fun x : list ⌊r⌋ => map inr (map g x)))
          by apply map_map.
        reflexivity.
  Qed.

  Global Instance hom_seq p q r s f g :
    @homomorphism p q f -> @homomorphism r s g -> @homomorphism (p⋅r) (q⋅s) (f ⨝ g).
  Proof.
    intros Hf Hg;split.
    - typeclasses eauto.
    - intros [];simpl;apply hom_Lbl.
    - intros [x|x] [y|y];simpl;apply hom_Ord||tauto.
    - simpl.
      repeat rewrite map_map||rewrite map_app.
      erewrite map_ext by apply map_map.
      erewrite (map_ext (fun x : list ⟨ PomType r ⟩ => map (f ⨝ g) (map inr x)))
        by apply map_map.
      apply smaller_set_app_Proper.
      + rewrite <- (@hom_Boxes _ _ _ Hf),map_map.
        erewrite (map_ext (fun x : list ⌊p⌋ => map inl (map f x)))
          by apply map_map.
        reflexivity.
      + rewrite <- (@hom_Boxes _ _ _ Hg),map_map.
        erewrite (map_ext (fun x : list ⌊r⌋ => map inr (map g x)))
          by apply map_map.
        reflexivity.
  Qed.

  Global Instance iso_par p q r s f g :
    @isomorphism p q f -> @isomorphism r s g -> @isomorphism (p∥r) (q∥s) (f ⨝ g).
  Proof.
    intros Hf Hg;split.
    - typeclasses eauto.
    - intros [];simpl;apply iso_Lbl.
    - intros [x|x] [y|y];simpl;apply iso_Ord||tauto.
    - simpl.
      repeat rewrite map_map||rewrite map_app.
      erewrite map_ext by apply map_map.
      erewrite (map_ext (fun x : list ⟨ PomType r ⟩ => map (f ⨝ g) (map inr x)))
        by apply map_map.
      apply equiv_set_app_Proper.
      + rewrite <- (@iso_Boxes _ _ _ Hf),map_map.
        erewrite (map_ext (fun x : list ⌊p⌋ => map inl (map f x)))
          by apply map_map.
        reflexivity.
      + rewrite <- (@iso_Boxes _ _ _ Hg),map_map.
        erewrite (map_ext (fun x : list ⌊r⌋ => map inr (map g x)))
          by apply map_map.
        reflexivity.
  Qed.

  Global Instance iso_seq p q r s f g :
    @isomorphism p q f -> @isomorphism r s g -> @isomorphism (p⋅r) (q⋅s) (f ⨝ g).
  Proof.
    intros Hf Hg;split.
    - typeclasses eauto.
    - intros [];simpl;apply iso_Lbl.
    - intros [x|x] [y|y];simpl;apply iso_Ord||tauto.
    - simpl.
      repeat rewrite map_map||rewrite map_app.
      erewrite map_ext by apply map_map.
      erewrite (map_ext (fun x : list ⟨ PomType r ⟩ => map (f ⨝ g) (map inr x)))
        by apply map_map.
      apply equiv_set_app_Proper.
      + rewrite <- (@iso_Boxes _ _ _ Hf),map_map.
        erewrite (map_ext (fun x : list ⌊p⌋ => map inl (map f x)))
          by apply map_map.
        reflexivity.
      + rewrite <- (@iso_Boxes _ _ _ Hg),map_map.
        erewrite (map_ext (fun x : list ⌊r⌋ => map inr (map g x)))
          by apply map_map.
        reflexivity.
  Qed.
  
  Global Instance seqProd_Proper_subs :
    Proper (subsume ==> subsume ==> subsume) prod.
  Proof. intros p1 p2 (ϕ&h) p3 p4 (ϕ'&h');exists (ϕ⨝ϕ');typeclasses eauto. Qed.
  
  Global Instance sumProd_Proper_subs :
    Proper (subsume ==> subsume ==> subsume) par.
  Proof. intros p1 p2 (ϕ&h) p3 p4 (ϕ'&h');exists (ϕ⨝ϕ');typeclasses eauto. Qed.

  Definition assoc_morph1 a b c : ⟨(a ⊎ b) ⊎ c⟩ -> ⟨a ⊎ (b ⊎ c)⟩ :=
    fun x  => match x with
           | inl (inl a) => inl a
           | inl (inr b) => inr (inl b)
           | inr c => inr (inr c)
           end.
  Definition assoc_morph2 a b c : ⟨a ⊎ (b ⊎ c)⟩ -> ⟨(a ⊎ b) ⊎ c⟩ :=
    fun x  => match x with
           | inl a => inl (inl a)
           | inr (inl b) => inl (inr b)
           | inr (inr c) => inr c
           end.

  Global Instance bijective_assoc_morph1 a b c : bijective (@assoc_morph1 a b c).
  Proof.
    apply bijective_inverse_iff;exists (@assoc_morph2 a b c);split;
      intros [|[]]||intros [[]|];reflexivity.
  Qed.
  Global Instance bijective_assoc_morph2 a b c : bijective (@assoc_morph2 a b c).
  Proof.
    apply bijective_inverse_iff;exists (@assoc_morph1 a b c);split;
      intros [|[]]||intros [[]|];reflexivity.
  Qed.

  Lemma assoc_morph1_inverse a b c : (@assoc_morph1 a b c) ∘ (@assoc_morph2 a b c) ≃ id.
  Proof. intros [|[]];reflexivity. Qed.

  Lemma assoc_morph2_inverse a b c : (@assoc_morph2 a b c) ∘ (@assoc_morph1 a b c) ≃ id.
  Proof. intros [[]|];reflexivity. Qed.

  Global Instance assoc_morph2_seq_iso p q r :
    @isomorphism (p⋅(q⋅r)) ((p⋅q)⋅r) (@assoc_morph2 (PomType p) (PomType q) (PomType r)).
  Proof.
    split.
    - typeclasses eauto.
    - intros [|[]];reflexivity.
    - intros [|[]] [|[]];reflexivity.
    - simpl;repeat rewrite map_app||rewrite map_map||rewrite app_ass.
      repeat apply equiv_set_app_Proper;(erewrite map_ext;[reflexivity|]);
        intro;repeat rewrite map_map;simpl;reflexivity.
  Qed.
      
  Global Instance assoc_morph1_seq_iso p q r :
    @isomorphism ((p⋅q)⋅r) (p⋅(q⋅r)) (@assoc_morph1 (PomType p) (PomType q) (PomType r)).
  Proof.
    rewrite inverse_unique.
    - eapply (@inverse_isomorphism _ _ _ (@assoc_morph2_seq_iso p q r)).
    - apply assoc_morph2_inverse.
  Qed.
  
  Global Instance assoc_morph2_par_iso p q r :
    @isomorphism (p∥(q∥r)) ((p∥q)∥r) (@assoc_morph2 (PomType p) (PomType q) (PomType r)).
  Proof.
    split.
    - typeclasses eauto.
    - intros [|[]];reflexivity.
    - intros [|[]] [|[]];reflexivity.
    - simpl;repeat rewrite map_app||rewrite map_map||rewrite app_ass.
      repeat apply equiv_set_app_Proper;(erewrite map_ext;[reflexivity|]);
        intro;repeat rewrite map_map;simpl;reflexivity.
  Qed.
  Global Instance assoc_morph1_par_iso p q r :
    @isomorphism ((p∥q)∥r) (p∥(q∥r)) (@assoc_morph1 (PomType p) (PomType q) (PomType r)).
  Proof.
    rewrite inverse_unique.
    - eapply (@inverse_isomorphism _ _ _ (@assoc_morph2_par_iso p q r)).
    - apply assoc_morph2_inverse.
  Qed.

  Instance SeqMonoid_Pomsets : Monoid Pomset sequiv prod un.
  Proof.
    split.
    - intros a b E c d E'.
      apply antisymmetry;apply seqProd_Proper_subs;rewrite E||rewrite E';reflexivity.
    - intros A B C;exists (@assoc_morph1 (PomType A) (PomType B) (PomType C));
        typeclasses eauto.
    - split.
      + intros P; exists (fun x => inr x);split.
        * split;split.
          -- intros x y E;inversion E;subst;reflexivity.
          -- intros [[]|x];exists x;reflexivity.
        * intro;reflexivity.
        * intros ? ?;reflexivity.
        * simpl;reflexivity.
      + intros P; exists (fun x => inl x);split.
        * split;split.
          -- intros x y E;inversion E;subst;reflexivity.
          -- intros [x|[]];exists x;reflexivity.
        * intro;reflexivity.
        * intros ? ?;reflexivity.
        * simpl;rewrite app_nil_r;reflexivity.
  Qed.

  Instance ParMonoid_Pomsets : Monoid Pomset sequiv par un.
  Proof.
    split.
    - intros a b E c d E'.
      apply antisymmetry;apply sumProd_Proper_subs;rewrite E||rewrite E';reflexivity.
    - intros A B C;exists (@assoc_morph1 (PomType A) (PomType B) (PomType C));
        typeclasses eauto.
    - split.
      + intros P; exists (fun x => inr x);split.
        * split;split.
          -- intros x y E;inversion E;subst;reflexivity.
          -- intros [[]|x];exists x;reflexivity.
        * intro;reflexivity.
        * intros ? ?;reflexivity.
        * simpl;reflexivity.
      + intros P; exists (fun x => inl x);split.
        * split;split.
          -- intros x y E;inversion E;subst;reflexivity.
          -- intros [x|[]];exists x;reflexivity.
        * intro;reflexivity.
        * intros ? ?;reflexivity.
        * simpl;rewrite app_nil_r;reflexivity.
  Qed.

  Definition switch s t : ⟨s ⊎ t⟩ -> ⟨t ⊎ s⟩ :=
    fun x => match x with
          | inl x => inr x
          | inr x => inl x
          end.

  Lemma switch_switch s t : @switch s t ∘ @switch t s ≃ id.
  Proof. intros [|];reflexivity. Qed.

  Global Instance switch_iso p q : @isomorphism (p∥q) (q∥p) (@switch _ _).
  Proof.
    split.
    - apply bijective_inverse_iff;exists (@switch _ _);split;apply switch_switch.
    - intros [];reflexivity.
    - intros [] [];reflexivity.
    - simpl;repeat rewrite map_app||rewrite map_map;rewrite app_comm.
      apply equiv_set_app_Proper;(erewrite map_ext;[reflexivity|]);
        intro;rewrite map_map;reflexivity.
  Qed.
  
  Instance sumPomsets_comm_subs : @Commutative Pomset sequiv par.
  Proof. intros p q;exists (@switch _ _);typeclasses eauto. Qed.

  Global Instance PomsetsBiMonoid : BiMonoid Pomset sequiv prod par un.
  Proof.
    split.
    - apply SeqMonoid_Pomsets.
    - apply ParMonoid_Pomsets.
    - apply sumPomsets_comm_subs.
  Qed.

  Definition exchange_map a b c d : ⌊(a ⋅ c) ∥ (b ⋅ d)⌋ ->  ⌊(a ∥ b) ⋅ (c ∥ d)⌋ :=
    fun x => match x with
          | inl (inl a) => inl (inl a)
          | inl (inr c) => inr (inl c)
          | inr (inl b) => inl (inr b)
          | inr (inr d) => inr (inr d)
          end.

  Lemma exchange_map_hom a b c d : homomorphism (@exchange_map a b c d).
  Proof.
    split.
    - split;split.
      + intros [[]|[]] [[]|[]] E;inversion E;reflexivity.
      + intros [[x|x]|[x|x]].
        * exists (inl(inl x));reflexivity.
        * exists (inr(inl x));reflexivity.
        * exists (inl(inr x));reflexivity.
        * exists (inr(inr x));reflexivity.
    - intros [[]|[]];reflexivity.
    - intros [[]|[]] [[]|[]];simpl;tauto.
    - simpl;repeat rewrite map_app||rewrite map_map.
      rewrite app_ass,<-(app_ass (map _ (Boxes c))).
      rewrite (app_comm (map _ (Boxes c))).
      repeat rewrite app_ass; repeat apply smaller_set_app_Proper;
        (erewrite map_ext;[reflexivity|intro;repeat rewrite map_map;reflexivity]).
  Qed.
            
  Lemma exchange_law a b c d: (a ∥ b) ⋅ (c ∥ d) ⊑ (a ⋅ c) ∥ (b ⋅ d).
  Proof. eexists;apply exchange_map_hom. Qed.

  Lemma Pomset_box_hom : forall P : Pomset, @homomorphism P (@box _ boxPomsets P) id.
  Proof.
    split;simpl.
    - split;split.
      + tauto.
      + intro y;exists y;reflexivity.
    - reflexivity.
    - intros ? ? I;apply I.
    - simpl.
      erewrite map_ext,map_id by apply map_id.
      case_eq ⟪PomType P⟫.
      + case_eq (Boxes P);[reflexivity|].
        intros [|e ?] ? E F;exfalso.
        * eapply Pomset_hnil;rewrite E;now left.
        * pose proof (domain_spec e) as FF.
          rewrite F in FF;apply FF.
      + intros ? ? _.
        apply incl_smaller_sets,incl_tl;reflexivity.
  Qed.

  Lemma Pomset_box_inf P : ▢ P ⊑ P.
  Proof. exists id;apply Pomset_box_hom. Qed.
  
  Lemma Pomset_box_box P : ▢ (▢ P) ≃ ▢ P.
  Proof.
    apply antisymmetry;[apply Pomset_box_inf|].
    exists id;split.
    - typeclasses eauto.
    - reflexivity.
    - unfold id;simpl;tauto. 
    - simpl.
      erewrite map_ext,map_id by apply map_id.
      case_eq ⟪PomType P⟫;[reflexivity|].
      intros e l <-.
      apply incl_smaller_sets;intro;simpl;tauto.
  Qed.

  Lemma Pomset_box_unit : ▢ 𝟭 ≃ 𝟭.
  Proof.
    unfold un,box,boxPomsets,unPomsets;simpl;exists id;simpl;split;
      unfold id in *;simpl in *;firstorder tauto.
  Qed.

  Global Instance box_proper_inf : Proper (subsume ==> subsume) box.
  Proof.
    intros P Q (ϕ,I).
    exists ϕ;split. 
    - apply I.
    - apply I.
    - apply I.
    - simpl.
      case_eq ⟪PomType Q⟫.
      + intros;apply incl_smaller_sets,incl_nil.
      + intros e l E;rewrite <- E;simpl.
        case_eq ⟪PomType P⟫.
        * intro F;exfalso.
          pose proof (domain_spec (ϕ e)) as Ie;rewrite F in Ie;apply Ie.
        * intros x m E';rewrite <- E'.
          apply smaller_set_cons_Proper;[|apply I].
          symmetry;apply domain_equiv.
          intros y _;apply in_map_iff.
          destruct (@is_surjective _ _ ϕ _ y) as (y'&<-);exists y'.
          split;[reflexivity|apply domain_spec].
  Qed.
  
  Global Instance box_proper : Proper (sequiv ==> sequiv) box.
  Proof.
    intros P Q E;apply antisymmetry;apply Pomset_smaller_PartialOrder in E;
      apply box_proper_inf,E.
  Qed.
    
  Global Instance sizePomset : Size Pomset := fun P => ⎢PomType P⎥.

  Lemma sizePomset_subsumption P Q : P ⊑ Q -> ⎢P⎥ = ⎢Q⎥.
  Proof. intros (ϕ&h);eapply bijective_size,h. Qed.
  Lemma sizePomset_equiv P Q : P ≃ Q -> ⎢P⎥ = ⎢Q⎥.
  Proof. intros (ϕ&h);eapply bijective_size,h. Qed.

  Lemma size_0_eq_unit P : ⎢P⎥ = 0 -> P ≃ 𝟭.
  Proof.
    intro hyp.
    case_eq (domain (PomType P)).
    - intros D.
      destruct (exists_unique_function_from_empty_type D (PomType 𝟭)) as (ϕ&_).
      symmetry;exists ϕ;split.
      + split;split.
        * intros x;exfalso.
          pose proof (domain_spec x) as I;rewrite D in I;apply I.
        * intros y;exfalso;apply y.
      + intros x;exfalso.
        pose proof (domain_spec x) as I;rewrite D in I;apply I.
      + intros x;exfalso.
        pose proof (domain_spec x) as I;rewrite D in I;apply I.
      + case_eq (Boxes P);[reflexivity|].
        intros [|x ?] ? EB;exfalso.
        * destruct P as [t λ o B po nI];simpl in *.
          apply nI;rewrite EB;now left.
        * pose proof (domain_spec x) as I;rewrite D in I;apply I.
    - intros ? ? E;exfalso.
      unfold size,sizePomset,size,size_type in hyp.
      rewrite E in hyp;rsimpl in hyp;discriminate.
  Qed.
  Lemma size_1_eq_atomic P : ⎢P⎥ = 1 -> exists a, P ≃ AtomicPomset a \/ P ≃ ▢ (AtomicPomset a).
  Proof.
    destruct P as [t λ o B po nI];simpl in *.
    unfold size,sizePomset,size,size_type;simpl.
    case_eq (domain t);[rsimpl;discriminate|intros e [|] D;[intros _|rsimpl;discriminate]].
    assert (eq_e : forall x, x = e)
      by (intro x;symmetry;cut(x ∈ [e]);[simpl;tauto|rewrite <- D;apply domain_spec]).
    assert (eq_l : forall l, l ≈ [e] \/ l = [])
      by (intros [|x l];[right;reflexivity
                        |left;apply antisymmetry;
                         [intros ? _;left;symmetry
                         |intros ? [<-|F];[left|exfalso;apply F]];apply eq_e]).
    exists (λ e).
    remember B as boxes;destruct boxes as [|β ?];[left|right];
      symmetry;exists (fun _ => υ);repeat split.
    - intros x y _;rewrite eq_e;apply eq_e.
    - exact e.
    - destruct y;reflexivity.
    - simpl;intro a;rewrite (eq_e a);reflexivity.
    - intros _;rewrite (eq_e a),(eq_e a');reflexivity.
    - reflexivity.
    - reflexivity.
    - intros x y _;rewrite eq_e;apply eq_e.
    - exact e.
    - destruct y;reflexivity.
    - simpl;intro a;rewrite (eq_e a);reflexivity.
    - intros _;rewrite (eq_e a),(eq_e a');reflexivity.
    - intros x I;exists [υ];split;[now left|].
      apply in_map_iff in I as (γ&<-&Iγ);simpl in *.
      destruct (eq_l γ) as [->| ->];
        [|exfalso;apply nI;now left].
      reflexivity.
    - intros ? [<-|F];[|exfalso;apply F];simpl.
      exists (map (fun _ : type t => υ) β);split;[now left|].
      destruct (eq_l β) as [-> | ->];
        [|exfalso;apply nI;now left].
      reflexivity.
  Qed.

  Lemma Boxes_box_spec P :
    P ≃ 𝟭 \/ Boxes (@box _ boxPomsets P) = ⟪PomType P⟫ :: (Boxes P).
  Proof.
    unfold box,boxPomsets;simpl.
    case_eq ⟪PomType P⟫.
    - intro E;left;apply size_0_eq_unit.
      unfold size,sizePomset,size,size_type;rewrite E;reflexivity.
    - intros t l E;right;reflexivity.
  Qed.
    
  Section pure_pomsets.
    Definition Pure (P : Pomset) := Boxes P = [].

    Lemma Pure_empty : Pure 𝟭.
    Proof. reflexivity. Qed.
    Lemma Pure_Atomic a : Pure (AtomicPomset a).
    Proof. reflexivity. Qed.

    Lemma Pure_seq P Q : Pure P -> Pure Q -> Pure (P ⋅ Q).
    Proof.
      destruct P as [tp lp rp bp pop], Q as [tq lq rq bq poq].
      unfold Pure,prod,seqPomsets;simpl.
      destruct bp;[|discriminate].
      destruct bq;[|discriminate].
      reflexivity.
    Qed.
    
    Lemma Pure_par P Q : Pure P -> Pure Q -> Pure (P ∥ Q).
    Proof.
      destruct P as [tp lp rp bp pop], Q as [tq lq rq bq poq].
      unfold Pure,par,sumPomsets;simpl.
      destruct bp;[|discriminate].
      destruct bq;[|discriminate].
      reflexivity.
    Qed.

    Lemma Pure_subsumption_upwards_closed P Q : P ⊑ Q -> Pure P -> Pure Q.
    Proof.
      intros (ϕ&Iso). 
      unfold Pure in *;simpl in *.
      intros hp;case_eq (Boxes Q);[reflexivity|].
      intros b B E;exfalso.
      destruct (@hom_Boxes _ _ _ _ (map ϕ b)) as (x&Ix&_).
      - rewrite E;now left.
      - revert Ix;rewrite hp;simpl;tauto.
    Qed.

    Corollary Pure_equiv_closed P Q : P ≃ Q -> Pure P <-> Pure Q.
    Proof. intros E;split;apply Pure_subsumption_upwards_closed;rewrite E;reflexivity. Qed.

    Remark Pure_box_unit P : Pure (▢ P) -> P ≃ 𝟭.
    Proof.
      destruct P as [t l r b p];unfold Pure,box;simpl.
      case_eq (domain t);[|discriminate].
      intros D _;apply size_0_eq_unit.
      unfold size,sizePomset,size,size_type;simpl.
      rewrite D;reflexivity.
    Qed.
  End pure_pomsets.

  Class Well_nested P :=
    well_nested :
      forall α β, α ∈ Boxes P -> β ∈ Boxes P -> (α ⊆ β \/ β ⊆ α \/ (forall a, ~ a ∈ α \/ ~ a ∈ β)).

  Class Left_atomic P :=
    left_atomic :
      forall β x, β ∈ Boxes P -> ~ x ∈ β -> forall a b, a ∈ β -> b ∈ β -> x ≤[P] a <-> x ≤[P] b.

  Class Right_atomic P :=
    right_atomic :
      forall β x, β ∈ Boxes P -> ~ x ∈ β -> forall a b, a ∈ β -> b ∈ β -> a ≤[P] x <-> b ≤[P] x.

  Class WellFormed P :=
    {
      wf_wn :> Well_nested P;
      wf_la :> Left_atomic P;
      wf_ra :> Right_atomic P 
    }.
    
  Definition Convex P (β : list ⌊P⌋) :=
    β <> [] /\ forall a c b, a≤[P]b -> b ≤[P] c -> a ∈ β -> c ∈ β -> b ∈ β.

  Lemma WellFormed_Convex P β : WellFormed P -> β ∈ Boxes P -> Convex β.
  Proof.
    intros [] I;split.
    - destruct P as [p l r B po ne].
      unfold Convex in *;simpl in *.
      intros ->;apply ne,I.
    - intros a b c L1 L2 I1 I2.
      case_in c β;[assumption|].
      cut (c = a);[intros;subst;tauto|].
      apply antisymmetry;[|assumption].
      rewrite (left_atomic I I0);eassumption.
  Qed.

  Global Instance WellFormed_equiv : Proper (sequiv ==> iff) WellFormed.
  Proof.
    cut (forall P Q,  P ≃ Q -> WellFormed Q -> WellFormed P);
      [intros hyp P Q E;split;apply hyp;[symmetry|];assumption|].
    intros P Q (ϕ&Iso) W;split.
    - intros α' β' Iα Iβ.
      apply iso_Boxes in Iα as (α''&Iα&E).
      setoid_rewrite E;clear α' E.
      apply in_map_iff in Iα as (α&<-&Iα).
      apply iso_Boxes in Iβ as (β''&Iβ&E).
      setoid_rewrite E;clear β' E.
      apply in_map_iff in Iβ as (β&<-&Iβ).
      destruct (well_nested Iα Iβ) as [h|[h|h]].
      + left;rewrite h;reflexivity.
      + right;left;rewrite h;reflexivity.
      + right;right;intros a'.
        destruct (@is_surjective _ _ ϕ _ a') as (a&<-).
        repeat rewrite in_map_iff.
        destruct (h a) as [Ia|Ia];[left|right];intros (b&E&Ib);
          apply is_injective in E;subst;tauto.
    - intros β' x' Iβ.
      apply iso_Boxes in Iβ as (β''&Iβ&E).
      setoid_rewrite E;clear β' E.
      apply in_map_iff in Iβ as (β&<-&Iβ).
      setoid_rewrite in_map_iff.
      destruct (@is_surjective _ _ ϕ _ x') as (x&<-).
      intros nI;cut (~ x ∈ β);[clear nI;intros nI|intros I;apply nI;exists x;tauto].
      intros a' b' (a&<-&Ia) (b&<-&Ib).
      repeat rewrite <- iso_Ord.
      eapply left_atomic;eassumption.
    - intros β' x' Iβ.
      apply iso_Boxes in Iβ as (β''&Iβ&E).
      setoid_rewrite E;clear β' E.
      apply in_map_iff in Iβ as (β&<-&Iβ).
      setoid_rewrite in_map_iff.
      destruct (@is_surjective _ _ ϕ _ x') as (x&<-).
      intros nI;cut (~ x ∈ β);[clear nI;intros nI|intros I;apply nI;exists x;tauto].
      intros a' b' (a&<-&Ia) (b&<-&Ib).
      repeat rewrite <- iso_Ord.
      eapply right_atomic;eassumption.
  Qed.
      

  Lemma WellFormed_unit : WellFormed 𝟭.
  Proof. split;intros ? ? []. Qed.

  Lemma WellFormed_Atomic a : WellFormed (AtomicPomset a).
  Proof. split;intros ? ? []. Qed.

  Lemma WellFormed_box P : WellFormed P -> WellFormed (▢ P).
  Proof.
    intros W.
    destruct (Boxes_box_spec P) as [EP|EB];
      [rewrite EP,Pomset_box_unit;apply WellFormed_unit|].
    split.
    - intros a b.
      rewrite EB;simpl.
      intros [<-|Ia] [<-|Ib].
      + left;reflexivity.
      + right;left;intros ? _;apply domain_spec.
      + left;intros ? _;apply domain_spec.
      + apply W;assumption.
    - intros b x;rewrite EB;intros [<-|Ib] nI.
      + exfalso;apply nI,domain_spec.
      + unfold box,boxPomsets;simpl.
        eapply left_atomic;assumption.
    - intros b x;rewrite EB;intros [<-|Ib] nI.
      + exfalso;apply nI,domain_spec.
      + unfold box,boxPomsets;simpl.
        eapply right_atomic;assumption. 
  Qed.
  
  Lemma WellFormed_box_iff P : WellFormed P <-> WellFormed (▢ P).
  Proof.
    split;[apply WellFormed_box|].
    destruct (Boxes_box_spec P) as [EP|EB];
      [rewrite EP;intros _;apply WellFormed_unit|].
    intros [W L R];
      unfold Well_nested,Left_atomic,Right_atomic in *;
      rewrite EB in *;simpl in *;clear EB;split;intro;intros;auto.
    - apply (L β);auto.
    - apply (R β);auto.
  Qed.

  Lemma WellFormed_seq P Q : WellFormed P -> WellFormed Q -> WellFormed (P⋅Q).
  Proof.
    intros WP WQ;split.
    - intros α β;simpl;intros Ia Ib.
      rewrite in_app_iff in Ia,Ib.
      repeat rewrite in_map_iff in Ia,Ib.
      destruct Ia as [Ia|Ia];destruct Ia as (a&<-&Ia);
        destruct Ib as [Ib|Ib];destruct Ib as (b&<-&Ib).
      + destruct (well_nested Ia Ib) as [h|[h|h]].
        * left;rewrite h;reflexivity.
        * right;left;rewrite h;reflexivity.
        * right;right.
          intro x;repeat rewrite in_map_iff.
          destruct x as [x|x].
          -- destruct (h x) as [Ix|Ix].
             ++ left;intros (y&E&Iy);inversion E;subst;apply Ix,Iy.
             ++ right;intros (y&E&Iy);inversion E;subst;apply Ix,Iy.
          -- left;intros (y&E&Iy);inversion E.
      + right;right.
        intro x;repeat rewrite in_map_iff.
        destruct x as [x|x].
        * right;intros (y&E&Iy);inversion E.
        * left;intros (y&E&Iy);inversion E.
      + right;right.
        intro x;repeat rewrite in_map_iff.
        destruct x as [x|x].
        * left;intros (y&E&Iy);inversion E.
        * right;intros (y&E&Iy);inversion E.
      + destruct (well_nested Ia Ib) as [h|[h|h]].
        * left;rewrite h;reflexivity.
        * right;left;rewrite h;reflexivity.
        * right;right.
          intro x;repeat rewrite in_map_iff.
          destruct x as [x|x].
          -- right;intros (y&E&Iy);inversion E.
          -- destruct (h x) as [Ix|Ix].
             ++ left;intros (y&E&Iy);inversion E;subst;apply Ix,Iy.
             ++ right;intros (y&E&Iy);inversion E;subst;apply Ix,Iy.
    - intros β' x Iβ nI;simpl in Iβ.
      rewrite in_app_iff in Iβ.
      repeat rewrite in_map_iff in Iβ.
      destruct Iβ as [Iβ|Iβ];destruct Iβ as (β&<-&Iβ);destruct x as [x|x];
        intros a' b' Ia Ib;apply in_map_iff in Ia as (a&<-&Ia);
          apply in_map_iff in Ib as (b&<-&Ib);simpl;try reflexivity.
      + eapply left_atomic;try eassumption.
        intros Ix;apply nI,in_map_iff;exists x;tauto.
      + eapply left_atomic;try eassumption.
        intros Ix;apply nI,in_map_iff;exists x;tauto.
    - intros β' x Iβ nI;simpl in Iβ.
      rewrite in_app_iff in Iβ.
      repeat rewrite in_map_iff in Iβ.
      destruct Iβ as [Iβ|Iβ];destruct Iβ as (β&<-&Iβ);destruct x as [x|x];
        intros a' b' Ia Ib;apply in_map_iff in Ia as (a&<-&Ia);
          apply in_map_iff in Ib as (b&<-&Ib);simpl;try reflexivity.
      + eapply right_atomic;try eassumption.
        intros Ix;apply nI,in_map_iff;exists x;tauto.
      + eapply right_atomic;try eassumption.
        intros Ix;apply nI,in_map_iff;exists x;tauto.
  Qed.

  Lemma WellFormed_seq_iff P Q : WellFormed P /\ WellFormed Q <-> WellFormed (P⋅Q).
  Proof.
    split;[intros (h1&h2);apply WellFormed_seq;assumption|].
    intros [W L R].
    unfold Well_nested,Left_atomic,Right_atomic in *;simpl in *.
    setoid_rewrite in_app_iff in W;setoid_rewrite in_map_iff in W.
    setoid_rewrite in_app_iff in L;setoid_rewrite in_map_iff in L.
    setoid_rewrite in_app_iff in R;setoid_rewrite in_map_iff in R.
    split;split;simpl.
    - intros a b Ia Ib.
      destruct (W (map inl a) (map inl b)) as [I|[I|D]].
      + left;exists a;tauto.
      + left;exists b;tauto.
      + apply incl_map in I as (a'&E&I).
        apply map_injective_injective in E as <-.
        * left;assumption.
        * split;intros ? ? ee;inversion ee;tauto.
      + apply incl_map in I as (a'&E&I).
        apply map_injective_injective in E as <-.
        * right;left;assumption.
        * split;intros ? ? ee;inversion ee;tauto.
      + right;right.
        intros e;destruct (D (inl e)) as [h|h];[left|right];intro I;apply h,in_map_iff;exists e;
          tauto.
    - intros b x Ib Ix e f Ie If.
      apply (L (map inl b) (inl x)) with (a:=inl e) (b0:=inl f).
      + left;exists b;tauto.
      + intro I;apply Ix;apply in_map_iff in I as (y&Ey&Iy);inversion Ey;subst;tauto.
      + apply in_map_iff;exists e;tauto.
      + apply in_map_iff;exists f;tauto.
    - intros b x Ib Ix e f Ie If.
      apply (R (map inl b) (inl x)) with (a:=inl e) (b0:=inl f).
      + left;exists b;tauto.
      + intro I;apply Ix;apply in_map_iff in I as (y&Ey&Iy);inversion Ey;subst;tauto.
      + apply in_map_iff;exists e;tauto.
      + apply in_map_iff;exists f;tauto.
    - intros a b Ia Ib.
      destruct (W (map inr a) (map inr b)) as [I|[I|D]].
      + right;exists a;tauto.
      + right;exists b;tauto.
      + apply incl_map in I as (a'&E&I).
        apply map_injective_injective in E as <-.
        * left;assumption.
        * split;intros ? ? ee;inversion ee;tauto.
      + apply incl_map in I as (a'&E&I).
        apply map_injective_injective in E as <-.
        * right;left;assumption.
        * split;intros ? ? ee;inversion ee;tauto.
      + right;right.
        intros e;destruct (D (inr e)) as [h|h];[left|right];intro I;apply h,in_map_iff;exists e;
          tauto.
    - intros b x Ib Ix e f Ie If.
      apply (L (map inr b) (inr x)) with (a:=inr e) (b0:=inr f).
      + right;exists b;tauto.
      + intro I;apply Ix;apply in_map_iff in I as (y&Ey&Iy);inversion Ey;subst;tauto.
      + apply in_map_iff;exists e;tauto.
      + apply in_map_iff;exists f;tauto.
    - intros b x Ib Ix e f Ie If.
      apply (R (map inr b) (inr x)) with (a:=inr e) (b0:=inr f).
      + right;exists b;tauto.
      + intro I;apply Ix;apply in_map_iff in I as (y&Ey&Iy);inversion Ey;subst;tauto.
      + apply in_map_iff;exists e;tauto.
      + apply in_map_iff;exists f;tauto.
  Qed.
      
  Lemma WellFormed_par P Q : WellFormed P -> WellFormed Q -> WellFormed (P∥Q).
  Proof.
    intros WP WQ;split.
    - intros a' b' Ia Ib;simpl in Ia,Ib.
      rewrite in_app_iff in Ia,Ib.
      repeat rewrite in_map_iff in Ia,Ib.
      destruct Ia as [Ia|Ia];destruct Ia as (a&<-&Ia);
        destruct Ib as [Ib|Ib];destruct Ib as (b&<-&Ib).
      + destruct (well_nested Ia Ib) as [h|[h|h]].
        * left;rewrite h;reflexivity.
        * right;left;rewrite h;reflexivity.
        * right;right.
          intro x;repeat rewrite in_map_iff.
          destruct x as [x|x].
          -- destruct (h x) as [Ix|Ix].
             ++ left;intros (y&E&Iy);inversion E;subst;apply Ix,Iy.
             ++ right;intros (y&E&Iy);inversion E;subst;apply Ix,Iy.
          -- left;intros (y&E&Iy);inversion E.
      + right;right.
        intro x;repeat rewrite in_map_iff.
        destruct x as [x|x].
        * right;intros (y&E&Iy);inversion E.
        * left;intros (y&E&Iy);inversion E.
      + right;right.
        intro x;repeat rewrite in_map_iff.
        destruct x as [x|x].
        * left;intros (y&E&Iy);inversion E.
        * right;intros (y&E&Iy);inversion E.
      + destruct (well_nested Ia Ib) as [h|[h|h]].
        * left;rewrite h;reflexivity.
        * right;left;rewrite h;reflexivity.
        * right;right.
          intro x;repeat rewrite in_map_iff.
          destruct x as [x|x].
          -- right;intros (y&E&Iy);inversion E.
          -- destruct (h x) as [Ix|Ix].
             ++ left;intros (y&E&Iy);inversion E;subst;apply Ix,Iy.
             ++ right;intros (y&E&Iy);inversion E;subst;apply Ix,Iy.
    - intros β' x Iβ nI;simpl in Iβ.
      rewrite in_app_iff in Iβ.
      repeat rewrite in_map_iff in Iβ.
      destruct Iβ as [Iβ|Iβ];destruct Iβ as (β&<-&Iβ);destruct x as [x|x];
        intros a' b' Ia Ib;apply in_map_iff in Ia as (a&<-&Ia);
          apply in_map_iff in Ib as (b&<-&Ib);simpl;try reflexivity.
      + eapply left_atomic;try eassumption.
        intros Ix;apply nI,in_map_iff;exists x;tauto.
      + eapply left_atomic;try eassumption.
        intros Ix;apply nI,in_map_iff;exists x;tauto.
    - intros β' x Iβ nI;simpl in Iβ.
      rewrite in_app_iff in Iβ.
      repeat rewrite in_map_iff in Iβ.
      destruct Iβ as [Iβ|Iβ];destruct Iβ as (β&<-&Iβ);destruct x as [x|x];
        intros a' b' Ia Ib;apply in_map_iff in Ia as (a&<-&Ia);
          apply in_map_iff in Ib as (b&<-&Ib);simpl;try reflexivity.
      + eapply right_atomic;try eassumption.
        intros Ix;apply nI,in_map_iff;exists x;tauto.
      + eapply right_atomic;try eassumption.
        intros Ix;apply nI,in_map_iff;exists x;tauto.
  Qed.      
          
  Lemma WellFormed_par_iff P Q : WellFormed P /\ WellFormed Q <-> WellFormed (P∥Q).
  Proof.
    split;[intros (h1&h2);apply WellFormed_par;assumption|].
    intros [W L R].
    unfold Well_nested,Left_atomic,Right_atomic in *;
      repeat (simpl in * ).
    setoid_rewrite in_app_iff in W;setoid_rewrite in_map_iff in W.
    setoid_rewrite in_app_iff in L;setoid_rewrite in_map_iff in L.
    setoid_rewrite in_app_iff in R;setoid_rewrite in_map_iff in R.
    split;split;simpl.
    - intros a b Ia Ib.
      destruct (W (map inl a) (map inl b)) as [I|[I|D]].
      + left;exists a;tauto.
      + left;exists b;tauto.
      + apply incl_map in I as (a'&E&I).
        apply map_injective_injective in E as <-.
        * left;assumption.
        * split;intros ? ? ee;inversion ee;tauto.
      + apply incl_map in I as (a'&E&I).
        apply map_injective_injective in E as <-.
        * right;left;assumption.
        * split;intros ? ? ee;inversion ee;tauto.
      + right;right.
        intros e;destruct (D (inl e)) as [h|h];[left|right];intro I;apply h,in_map_iff;exists e;
          tauto.
    - intros b x Ib Ix e f Ie If.
      apply (L (map inl b) (inl x)) with (a:=inl e) (b0:=inl f).
      + left;exists b;tauto.
      + intro I;apply Ix;apply in_map_iff in I as (y&Ey&Iy);inversion Ey;subst;tauto.
      + apply in_map_iff;exists e;tauto.
      + apply in_map_iff;exists f;tauto.
    - intros b x Ib Ix e f Ie If.
      apply (R (map inl b) (inl x)) with (a:=inl e) (b0:=inl f).
      + left;exists b;tauto.
      + intro I;apply Ix;apply in_map_iff in I as (y&Ey&Iy);inversion Ey;subst;tauto.
      + apply in_map_iff;exists e;tauto.
      + apply in_map_iff;exists f;tauto.
    - intros a b Ia Ib.
      destruct (W (map inr a) (map inr b)) as [I|[I|D]].
      + right;exists a;tauto.
      + right;exists b;tauto.
      + apply incl_map in I as (a'&E&I).
        apply map_injective_injective in E as <-.
        * left;assumption.
        * split;intros ? ? ee;inversion ee;tauto.
      + apply incl_map in I as (a'&E&I).
        apply map_injective_injective in E as <-.
        * right;left;assumption.
        * split;intros ? ? ee;inversion ee;tauto.
      + right;right.
        intros e;destruct (D (inr e)) as [h|h];[left|right];intro I;apply h,in_map_iff;exists e;
          tauto.
    - intros b x Ib Ix e f Ie If.
      apply (L (map inr b) (inr x)) with (a:=inr e) (b0:=inr f).
      + right;exists b;tauto.
      + intro I;apply Ix;apply in_map_iff in I as (y&Ey&Iy);inversion Ey;subst;tauto.
      + apply in_map_iff;exists e;tauto.
      + apply in_map_iff;exists f;tauto.
    - intros b x Ib Ix e f Ie If.
      apply (R (map inr b) (inr x)) with (a:=inr e) (b0:=inr f).
      + right;exists b;tauto.
      + intro I;apply Ix;apply in_map_iff in I as (y&Ey&Iy);inversion Ey;subst;tauto.
      + apply in_map_iff;exists e;tauto.
      + apply in_map_iff;exists f;tauto.
  Qed.

  Definition Maximal P β :=
    β ∈ Boxes P /\ forall α, α ∈ (Boxes P) -> β ⊆ α -> α ≈ β.
  
  Arguments Maximal : clear implicits.

  Lemma Well_nested_Maximal P :
    Well_nested P -> Pure P \/ exists β, Maximal P β.
  Proof.
    unfold Well_nested.
    intros w. 
    unfold Maximal,Pure.
    destruct P as [p l r B po ne].
    simpl in *.
    clear po l r.
    induction B as [|β B];[tauto|].
    right;destruct IHB as [->|(βm&Iβm&Mβ)].
    - intro I;apply ne;now right.
    - intros a b Ia Ib.
      apply w;simpl;tauto.
    - exists β;simpl;split;[tauto|].
      intros ? [<-|F];[reflexivity|exfalso;apply F].
    - destruct (w β βm) as [L|[L|D]].
      + left;reflexivity.
      + right;assumption.
      + exists βm;split;[now right|].
        intros α [<-|I].
        * intros ?;apply antisymmetry;assumption.
        * apply Mβ;assumption.
      + exists β;split;[now left|].
        intros α [<-|I].
        * intros ?;apply antisymmetry;assumption.
        * intros h.
          apply antisymmetry;[|assumption].
          rewrite <- L in h.
          rewrite (Mβ _ I h);assumption.
      + exists βm;split;[now right|].
        intros α [<-|I].
        * intros I;exfalso.
          destruct βm as [|a ?].
          -- apply ne;right;apply Iβm.
          -- destruct (D a) as [nI|nI].
             ++ apply nI,I;now left.
             ++ apply nI;now left.
        * apply Mβ,I.
  Qed. 

      
  Lemma not_nil_in_undupEq t (l : list (list (type t))) : ~ [] ∈ l -> ~ [] ∈ (undupEq l).
  Proof.
    intros nI I.
    apply undupEq_eq in I as (b&Ib&Eb).
    destruct b as [|x b];[apply nI,Ib|].
    cut (x ∈ []);[intro F;apply F|].
    apply Eb;now left.
  Qed.

  Definition UndupBoxes P :=
    Build_Pomset (@ℓ P) (@Pomset_po P) (not_nil_in_undupEq (@Pomset_hnil P)).

  Lemma NoDupEq_UndupBoxes P : NoDupEq (Boxes (UndupBoxes P)).
  Proof. apply undupEq_NoDupEq. Qed.

  Lemma UndupBoxes_iso P : @isomorphism P (UndupBoxes P) id.
  Proof.
    split;simpl;auto.
    - typeclasses eauto.
    - unfold id;tauto.
    - erewrite map_ext by apply map_id.
      rewrite map_id.
      rewrite <- undupEq_eq;reflexivity.
  Qed.
  
  Lemma UndupBoxes_eq P : P ≃ UndupBoxes P.
  Proof. symmetry;eexists;eapply UndupBoxes_iso. Qed.

  Corollary UndupBoxes_WellFormed P : WellFormed P -> WellFormed (UndupBoxes P).
  Proof. rewrite (WellFormed_equiv (UndupBoxes_eq P));tauto. Qed.
  
  Definition DepthBox P (b : list ⌊P⌋) :=
    fold_right (fun b' acc => (if inclb b' b then S acc else acc)) 0 (Boxes P).
  Notation " Db[ P ] " := (@DepthBox P).

  Lemma DepthBox_incr P b1 b2 : b1 ⊆ b2 -> Db[P] b1 <= Db[P] b2.
  Proof.
    unfold DepthBox;intro Incl;induction (Boxes P);[reflexivity|].
    simpl.
    simpl in *.
    case_eq (inclb a b1);case_eq (inclb a b2);intros I1 I2;try lia.
    exfalso;apply not_true_iff_false in I1;apply I1,inclb_correct.
    apply inclb_correct in I2.
    rewrite I2;apply Incl.
  Qed.
  
  Lemma DepthBox_strict_decr P b1 b2 :
    b2 ∈ Boxes P -> b1 ⊆ b2 -> b1 ≈ b2 \/ Db[P] b1 < Db[P] b2.
  Proof.
    intros I1 I2.
    case_eq (inclb b2 b1);[intro Incl;left;apply antisymmetry;
                           [auto|apply inclb_correct,Incl]|].
    intro I3;right.
    unfold DepthBox.
    remember (Boxes P) as B.
    clear HeqB.
    induction B as [|b B];[simpl in *;tauto|].
    simpl in *.
    destruct I1 as [<-|I1].
    - simpl;case_eq (inclb b b);
        [|rewrite <- not_true_iff_false;intro F;exfalso;apply F,inclb_correct;reflexivity].
      intros _.
      rewrite I3.
      apply Lt.le_lt_n_Sm.
      revert I2;clear;intro I.
      induction B;[reflexivity|].
      simpl.
      case_eq (inclb a b);case_eq (inclb a b1);intros I1 I2;try lia.
      exfalso;apply not_true_iff_false in I2;apply I2,inclb_correct.
      apply inclb_correct in I1.
      rewrite I1;apply I.
    - simpl.
      pose proof I1 as ih;apply IHB in ih;clear IHB.
      case_eq (inclb b b2);case_eq (inclb b b1);try lia.
      intros F1 F2.
      exfalso;apply not_true_iff_false in F2;rewrite inclb_correct in F1,F2.
      apply F2;rewrite <- I2,F1;reflexivity.
  Qed.
  
  Remark DepthBox_bnd P b : Db[P] b <= ⎢Boxes P⎥.
  Proof.
    unfold DepthBox;induction (Boxes P);simpl;rsimpl.
    - reflexivity.
    - simpl in *;destruct (inclb a b);lia.
  Qed.

  Lemma DepthBox_0 P b : Db[P] b = 0 -> forall b', b' ∈ Boxes P -> ~ (b' ⊆ b).
  Proof.
    unfold DepthBox;induction (Boxes P);simpl;rsimpl;[tauto|].
    simpl in *.
    case_eq (inclb a b);[discriminate|].
    intros F ih b' [<-|Ib'].
    - intros h;apply not_true_iff_false in F;apply F,inclb_correct,h.
    - apply IHl;assumption.
  Qed.

  Definition independent P : relation ⌊P⌋ :=
    fun x y => ~ (x ≤[P] y) /\ ~ (y ≤[P] x).
  Arguments independent : clear implicits.
  Infix " ⫫[ P ] " := (independent P) (at level 80).

  Global Instance symmetric_independent P : Symmetric (independent P).
  Proof. intros x y;unfold independent;firstorder. Qed.
  
  Class N_free P :=
    nfree:  ~ (exists e1 e2 e3 e4, (e1 ≤[P] e2 /\ e1 ≤[P] e4 /\ e3 ≤[P] e4)
                              /\ e2 ⫫[P] e3 /\ e2 ⫫[P] e4 /\ e1 ⫫[P] e3).

  Lemma N_free_unit : N_free 𝟭.
  Proof. intros ([]&_). Qed.

  Lemma N_free_atomic x : N_free (AtomicPomset x).
  Proof. intros ([]&[]&[]&[]&_&(F&_)&_);apply F;reflexivity. Qed.

  Lemma N_free_seq P Q : N_free P -> N_free Q -> N_free (P⋅Q).
  Proof.
    intros N1 N2.
    intros (e1&e2&e3&e4&(I1&I2&I3)&(F1&F2)&(F3&F4)&(F5&F6)).
    destruct P,Q;simpl in *.
    destruct e1 as [e1|e1], e2 as [e2|e2], e3 as [e3|e3], e4 as [e4|e4];
      simpl in *;try tauto.
    - apply N1;exists e1,e2,e3,e4;repeat split;simpl;assumption.
    - apply N2;exists e1,e2,e3,e4;repeat split;simpl;assumption.
  Qed.

  Lemma N_free_par P Q : N_free P -> N_free Q -> N_free (P∥Q).
  Proof.
    intros N1 N2.
    intros (e1&e2&e3&e4&(I1&I2&I3)&(F1&F2)&(F3&F4)&(F5&F6)).
    destruct P,Q;simpl in *.
    destruct e1 as [e1|e1], e2 as [e2|e2], e3 as [e3|e3], e4 as [e4|e4];
      simpl in *;try tauto.
    - apply N1;exists e1,e2,e3,e4;repeat split;simpl;assumption.
    - apply N2;exists e1,e2,e3,e4;repeat split;simpl;assumption.
  Qed.

  Lemma N_free_box P : N_free P -> N_free (▢ P).
  Proof. unfold N_free,box,independent;destruct P;simpl;tauto. Qed.
  
  Lemma N_free_seq_iff P Q : N_free P /\ N_free Q <-> N_free (P⋅Q).
  Proof.
    split;[intros (N1&N2);apply N_free_seq;assumption|].
    intros N;split;intros (e1&e2&e3&e4&(I1&I2&I3)&(F1&F2)&(F3&F4)&(F5&F6)).
    - apply N;destruct P,Q;simpl in *.
      exists (inl e1),(inl e2),(inl e3),(inl e4);simpl;repeat split;simpl;tauto.
    - apply N;destruct P,Q;simpl in *.
      exists (inr e1),(inr e2),(inr e3),(inr e4);simpl;repeat split;simpl;tauto.
  Qed.

  Lemma N_free_par_iff P Q : N_free P /\ N_free Q <-> N_free (P∥Q).
  Proof.
    split;[intros (N1&N2);apply N_free_par;assumption|].
    intros N;split;intros (e1&e2&e3&e4&(I1&I2&I3)&(F1&F2)&(F3&F4)&(F5&F6)).
    - apply N;destruct P,Q;simpl in *.
      exists (inl e1),(inl e2),(inl e3),(inl e4);simpl;repeat split;simpl;tauto.
    - apply N;destruct P,Q;simpl in *.
      exists (inr e1),(inr e2),(inr e3),(inr e4);simpl;repeat split;simpl;tauto.
  Qed.

  Lemma N_free_box_iff P : N_free P <-> N_free (▢ P).
  Proof. unfold N_free,box,independent;destruct P;simpl;tauto. Qed.

  Class SP_Pomset P :=
    {
      sp_N_free :> N_free P;
      sp_wf :> WellFormed P;
      sp_dec :> decOrder(fun a b => a ≤[P]b);
    }.

  Lemma SP_Pomset_unit : SP_Pomset 𝟭.
  Proof.
    split.
    - apply N_free_unit.
    - apply WellFormed_unit.
    - intros [].
  Qed.

  Lemma SP_Pomset_atomic x : SP_Pomset (AtomicPomset x).
  Proof.
    split.
    - apply N_free_atomic.
    - apply WellFormed_Atomic.
    - intros [] [];left;reflexivity.
  Qed.

  Lemma SP_Pomset_seq P Q : SP_Pomset P -> SP_Pomset Q -> SP_Pomset (P⋅Q).
  Proof.
    intros [n1 w1 d1] [n2 w2 d2].
    split.
    - apply N_free_seq;assumption.
    - apply WellFormed_seq;assumption.
    - destruct P,Q;simpl in *;apply seqOrder_decOrder;assumption.
  Qed.

  Lemma SP_Pomset_par P Q : SP_Pomset P -> SP_Pomset Q -> SP_Pomset (P∥Q).
  Proof.
    intros [n1 w1 d1] [n2 w2 d2].
    split.
    - apply N_free_par;assumption.
    - apply WellFormed_par;assumption.
    - destruct P,Q;simpl in *;apply sumOrder_decOrder;assumption.
  Qed.

  Lemma SP_Pomset_box P : SP_Pomset P -> SP_Pomset (▢ P).
  Proof.
    intros [n w d];split.
    - apply N_free_box,n.
    - apply WellFormed_box,w.
    - destruct P;simpl in *;apply d.
  Qed.
  
  Lemma SP_Pomset_seq_left P Q : SP_Pomset (P⋅Q) -> SP_Pomset P.
  Proof.
    intros [n1 w1 d1].
    split.
    - apply N_free_seq_iff in n1;tauto. 
    - apply WellFormed_seq_iff in w1;tauto.
    - destruct P,Q;simpl in *.
      intros a b.
      destruct (d1 (inl a)(inl b));[left|right];simpl in *;tauto.
  Qed.

  Lemma SP_Pomset_seq_right P Q : SP_Pomset (P⋅Q) -> SP_Pomset Q.
  Proof.
    intros [n1 w1 d1].
    split.
    - apply N_free_seq_iff in n1;tauto. 
    - apply WellFormed_seq_iff in w1;tauto.
    - destruct P,Q;simpl in *.
      intros a b.
      destruct (d1 (inr a)(inr b));[left|right];simpl in *;tauto.
  Qed.

  Lemma SP_Pomset_par_left P Q : SP_Pomset (P∥Q) -> SP_Pomset P.
  Proof.
    intros [n1 w1 d1].
    split.
    - apply N_free_par_iff in n1;tauto. 
    - apply WellFormed_par_iff in w1;tauto.
    - destruct P,Q;simpl in *.
      intros a b.
      destruct (d1 (inl a)(inl b));[left|right];simpl in *;tauto.
  Qed.

  Lemma SP_Pomset_par_right P Q : SP_Pomset (P∥Q) -> SP_Pomset Q.
  Proof.
    intros [n1 w1 d1].
    split.
    - apply N_free_par_iff in n1;tauto. 
    - apply WellFormed_par_iff in w1;tauto.
    - destruct P,Q;simpl in *.
      intros a b.
      destruct (d1 (inr a)(inr b));[left|right];simpl in *;tauto.
  Qed.

  Lemma SP_Pomset_box_rev P : SP_Pomset (▢ P) -> SP_Pomset P.
  Proof.
    intros [n w d];split.
    - apply N_free_box_iff,n.
    - apply WellFormed_box_iff,w.
    - destruct P;simpl in *;apply d.
  Qed.

  Global Instance N_free_equiv : Proper (sequiv ==> iff) N_free.
  Proof.
    cut (forall P Q, P ≃ Q -> N_free P -> N_free Q);
      [intros h p q E;split;apply h;[|symmetry];assumption|].
    intros P Q (ϕ&Iso) n (e1&e2&e3&e4&(I1&I2&I3)&(L1&L2)&(L3&L4)&L5&L6).
    repeat rewrite (@iso_Ord _ _ _ Iso) in *.
    apply n;exists (ϕ e1),(ϕ e2),(ϕ e3),(ϕ e4);repeat split;assumption.
  Qed.
    
  Proposition SP_Pomset_equiv P Q :
    { ϕ : ⌊Q⌋ -> ⌊P⌋ | isomorphism ϕ }  -> SP_Pomset P -> SP_Pomset Q.
  Proof.
    intros (ϕ&I) [n w d];split.
    - eapply N_free_equiv,n;symmetry;exists ϕ;assumption. 
    - eapply WellFormed_equiv,w;symmetry;exists ϕ;assumption. 
    - intros a b.
      destruct (d (ϕ a) (ϕ b));[left|right];
        rewrite iso_Ord;assumption.
  Qed.

  Section patterns.
    Definition pat_N P e1 e2 e3 e4 :=
      ((e1 ≤[ P] e2) /\ (e1 ≤[ P] e4) /\ e3 ≤[ P] e4) /\
      (e2 ⫫[ P] e3) /\ (e2 ⫫[ P] e4) /\ e1 ⫫[ P] e3.
    Definition pat_WN P e1 e2 e3 B1 B2 :=
      B1 ∈ Boxes P /\ B2 ∈ Boxes P
      /\ e1 ∈ B1 /\ ~ (e1 ∈ B2)
      /\ e2 ∈ B1 /\ e2 ∈ B2
      /\ ~(e3 ∈ B1) /\ e3 ∈ B2.
    Definition pat_LAt P e1 e2 e3 B :=
      B ∈ Boxes P
      /\ ~( e1 ∈ B) /\ e2 ∈ B /\ e3 ∈ B
      /\ e1 ≤[P] e2
      /\ ~ (e1 ≤[P] e3).
    Definition pat_RAt P e1 e2 e3 B :=
      B ∈ Boxes P
      /\ ~( e1 ∈ B) /\ e2 ∈ B /\ e3 ∈ B
      /\ e2 ≤[P] e1
      /\ ~ (e3 ≤[P] e1).
    Definition pat_Cvx P e1 e2 e3 B :=
      B ∈ Boxes P
      /\ e1 ∈ B /\ ~(e2 ∈ B) /\ e3 ∈ B
      /\ e1≤[P] e2 /\ e2 ≤[P] e3.
    
    Lemma N_free_pat_N P :
      N_free P <-> ~ exists e1 e2 e3 e4, @pat_N P e1 e2 e3 e4.
    Proof. unfold N_free,pat_N;reflexivity. Qed.

    Lemma Well_nested_pat_WN P :
      Well_nested P <-> ~ exists e1 e2 e3 B1 B2, @pat_WN P e1 e2 e3 B1 B2.
    Proof.
      unfold Well_nested,pat_WN;split.
      - intros h (e1&e2&e3&B1&B2&IB1&IB2&I11&I12&I21&I22&I31&I32).
        destruct (h _ _ IB1 IB2) as [I|[I|D]].
        + apply I12,I,I11.
        + apply I31,I,I32.
        + destruct (D e2) as [I|I];apply I;assumption.
      - intros hyp B1 B2 IB1 IB2.
        case_eq (inclb B1 B2);[rewrite inclb_correct;tauto|].
        case_eq (inclb B2 B1);[rewrite inclb_correct;tauto|].
        intros h1 h2;right;right;intros e.
        case_in e B1;[|tauto].
        case_in e B2;[|tauto].
        exfalso;apply hyp.
        unfold inclb in h1,h2.
        apply forallb_false_exists in h2 as (e1&I11&I12).
        apply forallb_false_exists in h1 as (e3&I32&I31).
        rewrite inb_false in I12,I31.
        exists e1,e,e3,B1,B2;tauto.
    Qed.

    Lemma Left_atomic_pat_LAt P :
      decOrder (fun a b : ⌊ P ⌋ => a ≤[ P] b) -> 
      Left_atomic P <-> ~ exists e1 e2 e3 B, @pat_LAt P e1 e2 e3 B.
    Proof.
      intros D;unfold Left_atomic,pat_LAt;split.
      - intros h (e1&e2&e3&B&IB&I1&I2&I3&O1&O2).
        apply O2,(h _ _ IB I1 e2 e3);assumption.
      - intros F B e IB Ie a b Ia Ib.
        destruct (po_dec e a) as [O1|O1],(po_dec e b) as [O2|O2];try tauto.
        + exfalso;apply F;exists e,a,b,B;tauto.
        + exfalso;apply F;exists e,b,a,B;tauto.
    Qed.

    Lemma Right_atomic_pat_RAt P :
      decOrder (fun a b : ⌊ P ⌋ => a ≤[ P] b) -> 
      Right_atomic P <-> ~ exists e1 e2 e3 B, @pat_RAt P e1 e2 e3 B.
    Proof.
      intros D;unfold Left_atomic,pat_RAt;split.
      - intros h (e1&e2&e3&B&IB&I1&I2&I3&O1&O2).
        apply O2,(h _ _ IB I1 e2 e3);assumption.
      - intros F B e IB Ie a b Ia Ib.
        destruct (po_dec a e) as [O1|O1],(po_dec b e) as [O2|O2];try tauto.
        + exfalso;apply F;exists e,a,b,B;tauto.
        + exfalso;apply F;exists e,b,a,B;tauto.
    Qed.

    Lemma Convex_pat_Cvx P :
      (forall B, B ∈ Boxes P -> Convex B) <-> ~ exists e1 e2 e3 B, @pat_Cvx P e1 e2 e3 B.
    Proof.
      unfold Convex,pat_Cvx;split.
      - intros h (e1&e2&e3&B&IB&I1&I2&I3&O1&O2).
        pose proof (h _ IB) as (_&h').
        apply I2,(h' e1 e3);tauto.
      - intros h B IB;split.
        + intros ->;revert IB;destruct P;assumption.
        + intros a c b O1 O2 I1 I3.
          case_in b B;[assumption|].
          exfalso;apply h;exists a,b,c,B;tauto.  
    Qed.
      
  End patterns.
  
  Section independent_properties.
    Definition predicate_independence f (Φ : (Pomset -> Prop) -> Prop) :=
      exists P, ~ f P /\ forall g, Φ g -> g P.
    Definition independent_pred_list (Φ : list (Pomset -> Prop)) :=
      forall f, f ∈ Φ -> predicate_independence f (fun g => g ∈ Φ /\ g <> f).

    Context (x : X).
    
    Lemma independent_SP_Pomset :
      independent_pred_list [N_free;Well_nested;Left_atomic;Right_atomic].
    Proof.
      intros f I;repeat destruct I as [<-|I];try (exfalso;apply I).
      - set (t := bintree_of_nat ⎢ [1; 2; 3; 4] ⎥).
        set (l := fun _ : type t => x).
        set (f := 𝒯l [1;2;3;4] : type t -> nat).
        set (o := (fun x y =>
                     x=y
                     \/ (f x = 1 /\ f y = 2)
                     \/ (f x = 1 /\ f y = 4)
                     \/ (f x = 3 /\ f y = 4))
                  : relation (type t)).
        eexists (@Build_Pomset t l o [] _ _).
        Unshelve.
        + split.
          * intro h;apply h;clear h.
            simpl.
            exists (inl υ),(inr(inl υ)),(inr(inr (inl υ))),(inr (inr(inr(inl υ)))).
            unfold independent,o,f;simpl;firstorder discriminate.
          * intros g (I&N);repeat destruct I as [<-|I];
              (exfalso;apply I||apply N;reflexivity)||clear N;
              unfold Well_nested,Left_atomic,Right_atomic,N_free;simpl;try tauto.
        + split.
          * intro a;left;reflexivity.
          * intros a b c;intros [->|I1] [->|I2];(left;reflexivity)||right;try tauto.
            destruct I1 as [I1|[I1|I1]],I1 as (Ia&Ib);
              rewrite Ib in I2;destruct I2 as [I2|[I2|I2]],I2 as (F&_);discriminate.
          * intros a b [->|I1];[reflexivity|].
            intros [->|I2];[reflexivity|].
            destruct I1 as [I1|[I1|I1]],I1 as (Ia&Ib);
              rewrite Ia,Ib in I2;destruct I2 as [I2|[I2|I2]],I2 as (F&_);discriminate.
        + simpl;tauto.
      - set (t := bintree_of_nat ⎢ [1; 2; 3] ⎥).
        set (l := fun _ : type t => x).
        set (f := 𝒯l [1;2;3] : type t -> nat).
        set (o := (fun a b => a = b) : relation (type t)).
        eexists (@Build_Pomset t l o [[inl υ;inr(inl υ)];[inr(inl υ);inr(inr(inl υ))]] _ _).
        Unshelve.
        + split.
          * rewrite Well_nested_pat_WN;unfold pat_WN.
            intros h;apply h;clear h.
            exists (inl υ),(inr(inl υ)),(inr(inr (inl υ))),
            [inl υ;inr(inl υ)],[inr(inl υ);inr(inr(inl υ))];simpl;repeat split;
              intuition discriminate.
          * intros g (I&N);repeat destruct I as [<-|I];
              (exfalso;apply I||apply N;reflexivity)||clear N.
            -- apply N_free_pat_N;unfold pat_N,independent,o;simpl.
               intros (e1&e2&e3&e4&(->&->&->)&h);tauto.
            -- intros B a;simpl in *.
               intros _ Ia b c Ib Ic;unfold o;split;intros ->;exfalso;apply Ia;assumption.
            -- intros B a;simpl in *.
               intros _ Ia b c Ib Ic;unfold o;split;intros ->;exfalso;apply Ia;assumption.
        + split.
          * intro a;reflexivity.
          * intros a b c E1 E2;etransitivity;eassumption.
          * intros a b -> _;reflexivity.
        + simpl;intuition discriminate.
      - set (t := bintree_of_nat ⎢ [1; 2; 3] ⎥).
        set (l := fun _ : type t => x).
        set (f := 𝒯l [1;2;3] : type t -> nat).
        set (o := (fun a b => a = b \/ (a = inl υ /\ b = inr(inl υ))) : relation (type t)).
        eexists (@Build_Pomset t l o [[inr(inl υ);inr(inr(inl υ))]] _ _).
        Unshelve.
        + split.
          * rewrite Left_atomic_pat_LAt;unfold pat_LAt.
            -- intros h;apply h;clear h.
               exists (inl υ),(inr(inl υ)),(inr(inr (inl υ))),
               [inr(inl υ);inr(inr(inl υ))];simpl;repeat split;unfold o;
                 try intuition discriminate.
            -- intros a b;destruct_eqX a b;[left;left;reflexivity|].
               destruct a as [[]|a].
               ++ destruct b as [[]|[[]|b]].
                  ** right;intros _;apply N;reflexivity.
                  ** left;right;split;reflexivity.
                  ** right;intros [F|(_&F)];discriminate.
               ++ right;intros [F|(F&_)].
                  ** apply N,F.
                  ** discriminate.
          * intros g (I&N);repeat destruct I as [<-|I];
              (exfalso;apply I||apply N;reflexivity)||clear N.
            -- apply N_free_pat_N;unfold pat_N,independent,o;simpl.
               intros (e1&e2&e3&e4&([->|(->&->)]&[->|(E&->)]&[->|(->&E')])&h); tauto.
            -- intros B1 B2 [<-|F1] [<-|F2];try (exfalso;apply F1||apply F2).
               left;reflexivity.
            -- intros B a;simpl in *.
               intros [<-|F];[|exfalso;apply F].
               simpl.
               destruct a as [[]|[[]|[[]|[]]]];(intro F;exfalso;apply F;tauto)||intros _.
               unfold o;clear.
               intros a b [<-|[<-|F]];[| |exfalso;apply F];
                 (intros [<-|[<-|F]];[| |exfalso;apply F]);
                 split;intros [E|(E1&E2)];(left;reflexivity)||discriminate.
        + split.
          * intro a;left;reflexivity.
          * intros a b c [->|(->&->)] [<-|(->&->)];unfold o;tauto.
          * intros a b [->|(->&->)].
            -- reflexivity.
            -- intros [F|(F&_)];discriminate.
        + simpl;intuition discriminate.
      - set (t := bintree_of_nat ⎢ [1; 2; 3] ⎥).
        set (l := fun _ : type t => x).
        set (f := 𝒯l [1;2;3] : type t -> nat).
        set (o := (fun a b => a = b \/ (a = inl υ /\ b = inr(inl υ))) : relation (type t)).
        eexists (@Build_Pomset t l o [[inl υ;inr(inr(inl υ))]] _ _).
        Unshelve.
        + split.
          * rewrite Right_atomic_pat_RAt;unfold pat_RAt.
            -- intros h;apply h;clear h.
               exists (inr(inl υ)),(inl υ),(inr(inr (inl υ))),
               [inl υ;inr(inr(inl υ))];simpl;repeat split;unfold o;
                 try intuition discriminate.
            -- intros a b;destruct_eqX a b;[left;left;reflexivity|].
               destruct a as [[]|a].
               ++ destruct b as [[]|[[]|b]].
                  ** right;intros _;apply N;reflexivity.
                  ** left;right;split;reflexivity.
                  ** right;intros [F|(_&F)];discriminate.
               ++ right;intros [F|(F&_)].
                  ** apply N,F.
                  ** discriminate.
          * intros g (I&N);repeat destruct I as [<-|I];
              (exfalso;apply I||apply N;reflexivity)||clear N.
            -- apply N_free_pat_N;unfold pat_N,independent,o;simpl.
               intros (e1&e2&e3&e4&([->|(->&->)]&[->|(E&->)]&[->|(->&E')])&h); tauto.
            -- intros B1 B2 [<-|F1] [<-|F2];try (exfalso;apply F1||apply F2).
               left;reflexivity.
            -- intros B a;simpl in *.
               intros [<-|F];[|exfalso;apply F].
               simpl.
               destruct a as [[]|[[]|[[]|[]]]];(intro F;exfalso;apply F;tauto)||intros _.
               unfold o;clear.
               intros a b [<-|[<-|F]];[| |exfalso;apply F];
                 (intros [<-|[<-|F]];[| |exfalso;apply F]);
                 split;intros [E|(E1&E2)];(left;reflexivity)||discriminate.
        + split.
          * intro a;left;reflexivity.
          * intros a b c [->|(->&->)] [<-|(->&->)];unfold o;tauto.
          * intros a b [->|(->&->)].
            -- reflexivity.
            -- intros [F|(F&_)];discriminate.
        + simpl;intuition discriminate.
    Qed.

    Remark Left_atomic_independent_Convex :
      predicate_independence
        Left_atomic
        (fun p => p ∈ [ (fun P => forall B, B ∈ Boxes P -> Convex B);
                       N_free;Well_nested;Right_atomic]).
    Proof.
      set (t := bintree_of_nat ⎢ [1; 2; 3] ⎥).
      set (l := fun _ : type t => x).
      set (f := 𝒯l [1;2;3] : type t -> nat).
      set (o := (fun a b => a = b \/ (a = inl υ /\ b = inr(inl υ))) : relation (type t)).
      eexists (@Build_Pomset t l o [[inr(inl υ);inr(inr(inl υ))]] _ _).
      Unshelve.
      - split.
        + rewrite Left_atomic_pat_LAt;unfold pat_LAt.
          * intros h;apply h;clear h.
            exists (inl υ),(inr(inl υ)),(inr(inr (inl υ))),
            [inr(inl υ);inr(inr(inl υ))];simpl;repeat split;unfold o;
              try intuition discriminate.
          * intros a b;destruct_eqX a b;[left;left;reflexivity|].
            destruct a as [[]|a].
            -- destruct b as [[]|[[]|b]].
               ++ right;intros _;apply N;reflexivity.
               ++ left;right;split;reflexivity.
               ++ right;intros [F|(_&F)];discriminate.
            -- right;intros [F|(F&_)].
               ++ apply N,F.
               ++ discriminate.
        + intros g I;repeat destruct I as [<-|I]; try (exfalso;apply I).
          * intros ? [<-|F];[|exfalso;apply F].
            split;[discriminate|].
            unfold o;simpl.
            intros ? ? ? [->|(->&->)] [<-|(E&->)];intuition.
          * apply N_free_pat_N;unfold pat_N,independent,o;simpl.
            intros (e1&e2&e3&e4&([->|(->&->)]&[->|(E&->)]&[->|(->&E')])&h); tauto.
          * intros B1 B2 [<-|F1] [<-|F2];try (exfalso;apply F1||apply F2).
            left;reflexivity.
          * intros B a;simpl in *.
            intros [<-|F];[|exfalso;apply F].
            simpl.
            destruct a as [[]|[[]|[[]|[]]]];(intro F;exfalso;apply F;tauto)||intros _.
            unfold o;clear.
            intros a b [<-|[<-|F]];[| |exfalso;apply F];
              (intros [<-|[<-|F]];[| |exfalso;apply F]);
              split;intros [E|(E1&E2)];(left;reflexivity)||discriminate.
      - split.
        + intro a;left;reflexivity.
        + intros a b c [->|(->&->)] [<-|(->&->)];unfold o;tauto.
        + intros a b [->|(->&->)].
          * reflexivity.
          * intros [F|(F&_)];discriminate.
      - simpl;intuition discriminate.
    Qed.
    Remark Right_atomic_independent_Convex :
      predicate_independence
        Right_atomic
        (fun p => p ∈ [ (fun P => forall B, B ∈ Boxes P -> Convex B);
                       N_free;Well_nested;Left_atomic]).
    Proof.
      set (t := bintree_of_nat ⎢ [1; 2; 3] ⎥).
      set (l := fun _ : type t => x).
      set (f := 𝒯l [1;2;3] : type t -> nat).
      set (o := (fun a b => a = b \/ (a = inl υ /\ b = inr(inl υ))) : relation (type t)).
      eexists (@Build_Pomset t l o [[inl υ;inr(inr(inl υ))]] _ _).
      Unshelve.
      - split.
        + rewrite Right_atomic_pat_RAt;unfold pat_RAt.
          * intros h;apply h;clear h.
            exists (inr(inl υ)),(inl υ),(inr(inr (inl υ))),
            [inl υ;inr(inr(inl υ))];simpl;repeat split;unfold o;
              try intuition discriminate.
          * intros a b;destruct_eqX a b;[left;left;reflexivity|].
            destruct a as [[]|a].
            -- destruct b as [[]|[[]|b]].
               ++ right;intros _;apply N;reflexivity.
               ++ left;right;split;reflexivity.
               ++ right;intros [F|(_&F)];discriminate.
            -- right;intros [F|(F&_)].
               ++ apply N,F.
               ++ discriminate.
        + intros g I;repeat destruct I as [<-|I]; try (exfalso;apply I).
          * intros ? [<-|F];[|exfalso;apply F].
            split;[discriminate|].
            unfold o;simpl.
            intros ? ? ? [->|(->&->)] [<-|(E&->)];intuition.
          * apply N_free_pat_N;unfold pat_N,independent,o;simpl.
            intros (e1&e2&e3&e4&([->|(->&->)]&[->|(E&->)]&[->|(->&E')])&h); tauto.
          * intros B1 B2 [<-|F1] [<-|F2];try (exfalso;apply F1||apply F2).
            left;reflexivity.
          * intros B a;simpl in *.
            intros [<-|F];[|exfalso;apply F].
            simpl.
            destruct a as [[]|[[]|[[]|[]]]];(intro F;exfalso;apply F;tauto)||intros _.
            unfold o;clear.
            intros a b [<-|[<-|F]];[| |exfalso;apply F];
              (intros [<-|[<-|F]];[| |exfalso;apply F]);
              split;intros [E|(E1&E2)];(left;reflexivity)||discriminate.
      - split.
        + intro a;left;reflexivity.
        + intros a b c [->|(->&->)] [<-|(->&->)];unfold o;tauto.
        + intros a b [->|(->&->)].
          * reflexivity.
          * intros [F|(F&_)];discriminate.
      - simpl;intuition discriminate.
    Qed.
  End independent_properties.


End pomsetdef.
Arguments Pomset : clear implicits.

Notation " ⌊ P ⌋ " :=⟨PomType P⟩.
Infix " ≤[ P ] " := (@PomOrd _ P) (at level 80).
Infix " <[ P ] " := (@strictOrd _ P) (at level 80).
Infix " ⫫[ P ] " := (@independent _ P) (at level 80).
Infix " ⨝ " := join_fun (at level 40).
  
Notation " Db[ P ] " := (@DepthBox _ P).

Arguments Maximal : clear implicits.
Arguments Maximal {X} P β.
Ltac case_order x y :=
  let h := fresh "I" in
  destruct (po_dec x y) as [h|h].

