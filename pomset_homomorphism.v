Require Import PeanoNat tools algebra Bool relations.
Require Import bsp_terms pomsets bsp_pomsets.
Require Import series_parallel_pomsets.
Require Import sub_pomsets pomset_isomorphism.

Remark subsets_Boxes_hnil {X} {P : Pomset X} {b} : b ⊆ Boxes P -> ~ [] ∈ b.
Proof. intros I F;eapply Pomset_hnil,I,F. Qed.

Remark subsets_app {A : Set} (l m : list A) x :
  x ∈ subsets (l++m) -> exists x1 x2, x = x1 ++ x2 /\ x1 ∈ subsets l /\ x2 ∈ subsets m.
Proof.
  revert x;induction l;intro x;simpl.
  - intros Ix;exists [],x;simpl;tauto.
  - rewrite in_app_iff;intros [Ix|Ix].
    + apply in_map_iff in Ix as (y&<-&Iy).
      apply IHl in Iy as (y1&y2&->&Iy1&Iy2).
      exists (a::y1),y2;split;[reflexivity|].
      split;[|assumption].
      apply in_app_iff;left;apply in_map_iff;exists y1;simpl;tauto.
    + apply IHl in Ix as (x1&x2&->&Ix1&Ix2).
      exists x1,x2;split;[reflexivity|].
      split;[|assumption].
      apply in_app_iff;now right.
Qed.

Remark subsets_map {A B : Set} (f : A -> B) l :
  subsets (map f l) = map (map f) (subsets l).
Proof.
  revert f;induction l;simpl;[reflexivity|].
  intro f; repeat rewrite IHl||rewrite map_map||rewrite map_app;simpl.
  reflexivity.
Qed.

Section s.
  Context {X : Set}.
  Context {decX : decidable_set X}.

  Lemma subsume_sound (s t : bsp_terms X) : s ⊑ t -> ⟦s⟧ ⊑ ⟦t⟧.
  Proof.
    intro h;induction h;rsimpl in *;auto.
    - apply soundness_bsp_terms in H as ->;reflexivity.
    - etransitivity;eassumption.
    - rewrite IHh,IHh0;reflexivity.
    - rewrite IHh,IHh0;reflexivity.
    - rewrite IHh;reflexivity.
    - apply exchange_law.
    - apply Pomset_box_inf.
  Qed.
  
  Global Instance bsp_subsumption_partialorder :
    PartialOrder equiv (@subsume (bsp_terms X) _).
  Proof.
    intros s t;unfold Basics.flip;split.
    - intros E;split;[|symmetry in E];auto.
    - intros (h1&h2).
      apply completeness_bsp_terms_iso,antisymmetry;apply subsume_sound;assumption.
  Qed.

  Class box_homomorphism (P Q : Pomset X) (f : ⌊P⌋ -> ⌊Q⌋) :=
    { box_bij : bijective f;
      box_Lbl : forall a : ⌊ P ⌋ , ℓ (f a) = ℓ a;
      box_Ord : forall a a' : ⌊ P ⌋ , a ≤[ P] a' <-> f a ≤[ Q] f a';
      box_Boxes : map (map f) (Boxes P) ≲ Boxes Q }.
  Class order_homomorphism (P Q : Pomset X) (f : ⌊P⌋ -> ⌊Q⌋) :=
    { order_bij : bijective f;
      order_Lbl : forall a : ⌊ P ⌋ , ℓ (f a) = ℓ a;
      order_Ord : forall a a' : ⌊ P ⌋ , a ≤[ P] a' -> f a ≤[ Q] f a';
      order_Boxes : map (map f) (Boxes P) ≃ Boxes Q }.

  Global Instance box_homomorphism_hom P Q f :
    box_homomorphism P Q f -> homomorphism f.
  Proof. intro h;split;try apply h. Qed.

  Global Instance order_homomorphism_hom P Q f :
    order_homomorphism P Q f -> homomorphism f.
  Proof. intro h;split;try apply h. Qed.

  Global Instance box_homomorphism_proper (P Q : Pomset X) :
    Proper (sequiv ==> iff) (box_homomorphism P Q).
  Proof.
    cut (forall P Q,Proper (sequiv ==> Basics.impl) (box_homomorphism P Q));
      [intros h f g E;split;apply h;[|symmetry];apply E|clear P Q].
    intros p q f g E H;split.
    - rewrite <- E;apply H.
    - intro;rewrite <- E;apply H.
    - intros ? ?;repeat rewrite <- E;apply H.
    - erewrite map_ext;[apply H|].
      apply map_ext;intro;symmetry;apply E.
  Qed.

  Global Instance order_homomorphism_proper (P Q : Pomset X) :
    Proper (sequiv ==> iff) (order_homomorphism P Q).
  Proof.
    cut (forall P Q,Proper (sequiv ==> Basics.impl) (order_homomorphism P Q));
      [intros h f g E;split;apply h;[|symmetry];apply E|clear P Q].
    intros p q f g E H;split.
    - rewrite <- E;apply H.
    - intro;rewrite <- E;apply H.
    - intros ? ?;repeat rewrite <- E;apply H.
    - erewrite map_ext;[apply H|].
      apply map_ext;intro;symmetry;apply E.
  Qed.

  Global Instance compose_box_homomorphism A B C (ϕ : ⌊A⌋ -> ⌊B⌋) (ψ : ⌊B⌋ -> ⌊C⌋) :
    box_homomorphism A B ϕ -> box_homomorphism B C ψ -> box_homomorphism A C (ψ∘ϕ).
  Proof.
    intros I1 I2;split.
    - apply bijective_compose;typeclasses eauto.
    - intros a;unfold Basics.compose.
      rewrite hom_Lbl,hom_Lbl;reflexivity.
    - intros a a';rewrite box_Ord,box_Ord;reflexivity.
    - unfold Basics.compose.
      erewrite <- map_ext by apply map_map.
      rewrite <- map_map,hom_Boxes,hom_Boxes.
      reflexivity.
  Qed.

  Global Instance compose_order_homomorphism A B C (ϕ : ⌊A⌋ -> ⌊B⌋) (ψ : ⌊B⌋ -> ⌊C⌋) :
    order_homomorphism A B ϕ -> order_homomorphism B C ψ -> order_homomorphism A C (ψ∘ϕ).
  Proof.
    intros I1 I2;split.
    - apply bijective_compose;typeclasses eauto.
    - intros a;unfold Basics.compose.
      rewrite order_Lbl,order_Lbl;reflexivity.
    - intros a a'.
      intros h;apply order_Ord,order_Ord in h.
      apply h.
    - unfold Basics.compose.
      erewrite <- map_ext by apply map_map.
      rewrite <- map_map,order_Boxes,order_Boxes.
      reflexivity.
  Qed.

  Global Instance box_hom_par p q r s f g :
    box_homomorphism p q f -> box_homomorphism r s g ->
    box_homomorphism (p∥r) (q∥s) (f ⨝ g).
  Proof.
    intros Hf Hg;split.
    - typeclasses eauto.
    - intros [];simpl;apply hom_Lbl.
    - intros [x|x] [y|y];simpl;apply box_Ord||tauto.
    - simpl.
      repeat rewrite map_map||rewrite map_app.
      erewrite map_ext by apply map_map.
      erewrite (map_ext (fun x : list ⟨ PomType r ⟩ => map (f ⨝ g) (map inr x)))
        by apply map_map.
      apply smaller_set_app_Proper.
      + rewrite <- (@box_Boxes _ _ _ Hf),map_map.
        erewrite (map_ext (fun x : list ⌊p⌋ => map inl (map f x)))
          by apply map_map.
        reflexivity.
      + rewrite <- (@box_Boxes _ _ _ Hg),map_map.
        erewrite (map_ext (fun x : list ⌊r⌋ => map inr (map g x)))
          by apply map_map.
        reflexivity.
  Qed.

  Global Instance box_hom_seq p q r s f g :
    box_homomorphism p q f -> box_homomorphism r s g ->
    box_homomorphism (p⋅r) (q⋅s) (f ⨝ g).
  Proof.
    intros Hf Hg;split.
    - typeclasses eauto.
    - intros [];simpl;apply box_Lbl.
    - intros [x|x] [y|y];simpl;apply box_Ord||tauto.
    - simpl.
      repeat rewrite map_map||rewrite map_app.
      erewrite map_ext by apply map_map.
      erewrite (map_ext (fun x : list ⟨ PomType r ⟩ => map (f ⨝ g) (map inr x)))
        by apply map_map.
      apply smaller_set_app_Proper.
      + rewrite <- (@box_Boxes _ _ _ Hf),map_map.
        erewrite (map_ext (fun x : list ⌊p⌋ => map inl (map f x)))
          by apply map_map.
        reflexivity.
      + rewrite <- (@box_Boxes _ _ _ Hg),map_map.
        erewrite (map_ext (fun x : list ⌊r⌋ => map inr (map g x)))
          by apply map_map.
        reflexivity.
  Qed.

  Global Instance order_hom_par p q r s f g :
    order_homomorphism p q f -> order_homomorphism r s g ->
    order_homomorphism (p∥r) (q∥s) (f ⨝ g).
  Proof.
    intros Hf Hg;split.
    - typeclasses eauto.
    - intros [];simpl;apply hom_Lbl.
    - intros [x|x] [y|y];simpl;apply order_Ord||tauto.
    - simpl.
      repeat rewrite map_map||rewrite map_app.
      erewrite map_ext by apply map_map.
      erewrite (map_ext (fun x : list ⟨ PomType r ⟩ => map (f ⨝ g) (map inr x)))
        by apply map_map.
      apply equiv_set_app_Proper.
      + rewrite <- (@order_Boxes _ _ _ Hf),map_map.
        erewrite (map_ext (fun x : list ⌊p⌋ => map inl (map f x)))
          by apply map_map.
        reflexivity.
      + rewrite <- (@order_Boxes _ _ _ Hg),map_map.
        erewrite (map_ext (fun x : list ⌊r⌋ => map inr (map g x)))
          by apply map_map.
        reflexivity.
  Qed.

  Global Instance order_hom_seq p q r s f g :
    order_homomorphism p q f -> order_homomorphism r s g ->
    order_homomorphism (p⋅r) (q⋅s) (f ⨝ g).
  Proof.
    intros Hf Hg;split.
    - typeclasses eauto.
    - intros [];simpl;apply order_Lbl.
    - intros [x|x] [y|y];simpl;apply order_Ord||tauto.
    - simpl.
      repeat rewrite map_map||rewrite map_app.
      erewrite map_ext by apply map_map.
      erewrite (map_ext (fun x : list ⟨ PomType r ⟩ => map (f ⨝ g) (map inr x)))
        by apply map_map.
      apply equiv_set_app_Proper.
      + rewrite <- (@order_Boxes _ _ _ Hf),map_map.
        erewrite (map_ext (fun x : list ⌊p⌋ => map inl (map f x)))
          by apply map_map.
        reflexivity.
      + rewrite <- (@order_Boxes _ _ _ Hg),map_map.
        erewrite (map_ext (fun x : list ⌊r⌋ => map inr (map g x)))
          by apply map_map.
        reflexivity.
  Qed.

  Definition box_subsumption := fun P Q => exists ϕ, box_homomorphism Q P ϕ.
  Definition order_subsumption := fun P Q => exists ϕ, order_homomorphism Q P ϕ.

  Infix " ⊑b " := box_subsumption (at level 80).
  Infix " ⊑o " := order_subsumption (at level 80).

  Lemma box_subsumption_equiv : subrelation sequiv box_subsumption.
  Proof. intros P Q (f&If);exists f;split;apply If. Qed.
  Lemma order_subsumption_equiv : subrelation sequiv order_subsumption.
  Proof. intros P Q (f&If);exists f;split;apply If. Qed.

  Global Instance box_subsumption_smaller : subrelation box_subsumption subsume.
  Proof. intros P Q (f&If);exists f;split;apply If. Qed.
  Global Instance order_subsumption_smaller : subrelation order_subsumption subsume.
  Proof. intros P Q (f&If);exists f;split;apply If. Qed.

  Global Instance box_subs_PreOrder : PreOrder (fun a b => a ⊑b b).
  Proof.
    split.
    - intros x;apply box_subsumption_equiv;reflexivity.
    - intros A B C (ϕ&h) (ϕ'&h');exists (ϕ∘ϕ');
        typeclasses eauto. 
  Qed.

  Lemma box_subs_PartialOrder : PartialOrder sequiv (fun a b => a ⊑b b).
  Proof.
    intros P Q;split;[intros E;split;apply box_subsumption_equiv;[|symmetry];assumption|].
    intros (h1&h2);apply antisymmetry;apply box_subsumption_smaller;assumption.
  Qed.

  Global Instance order_subs_PreOrder : PreOrder (fun a b => a ⊑o b).
  Proof.
    split.
    - intros x;apply order_subsumption_equiv;reflexivity.
    - intros A B C (ϕ&h) (ϕ'&h');exists (ϕ∘ϕ');
        typeclasses eauto. 
  Qed.

  Lemma order_subs_PartialOrder : PartialOrder sequiv (fun a b => a ⊑o b).
  Proof.
    intros P Q;split;[intros E;split;apply order_subsumption_equiv;[|symmetry];assumption|].
    intros (h1&h2);apply antisymmetry;apply order_subsumption_smaller;assumption.
  Qed.


  Global Instance seqProd_Proper_box_subs :
    Proper (box_subsumption ==> box_subsumption ==> box_subsumption) prod.
  Proof. intros p1 p2 (ϕ&h) p3 p4 (ϕ'&h');exists (ϕ⨝ϕ');typeclasses eauto. Qed.
  
  Global Instance sumProd_Proper_box_subs :
    Proper (box_subsumption ==> box_subsumption ==> box_subsumption) par.
  Proof. intros p1 p2 (ϕ&h) p3 p4 (ϕ'&h');exists (ϕ⨝ϕ');typeclasses eauto. Qed.

  Global Instance seqProd_Proper_order_subs :
    Proper (order_subsumption ==> order_subsumption ==> order_subsumption) prod.
  Proof. intros p1 p2 (ϕ&h) p3 p4 (ϕ'&h');exists (ϕ⨝ϕ');typeclasses eauto. Qed.
  
  Global Instance sumProd_Proper_order_subs :
    Proper (order_subsumption ==> order_subsumption ==> order_subsumption) par.
  Proof. intros p1 p2 (ϕ&h) p3 p4 (ϕ'&h');exists (ϕ⨝ϕ');typeclasses eauto. Qed.

  Proposition Homomorphism_factorisation_1 P Q f :
    homomorphism f ->
    exists R g h, box_homomorphism P R h /\ order_homomorphism R Q g /\ f ≃ g ∘ h.
  Proof.
    intros h.
    destruct (@dec_prop_powerset_bnd _ (fun b => exists l, l ∈ Boxes Q /\ map f b ≈ l)
                                     (𝒫 (PomType P))) as (B'&hB');
      [typeclasses eauto|].
    assert (hnil_B' : ~ [] ∈ B').
    - intro I.
      apply hB' in I as (_&[|x]&I&Ex);
        [clear Ex|cut (x ∈ []);[simpl;tauto|apply Ex;now left]].
      eapply Pomset_hnil,I. 
    - exists (Build_Pomset (@ℓ _ P) (@Pomset_po _ P) hnil_B');simpl.
      exists f,id;simpl.
      split;[split|split;[split|rewrite compose_id_r;reflexivity]].
      + apply bijective_id.
      + simpl;reflexivity.
      + simpl;reflexivity.
      + simpl.
        erewrite map_ext by apply map_id.
        rewrite map_id.
        intros β Iβ.
        destruct (𝒫_spec β) as (γ&Iγ&Eγ).
        exists γ;split;[|assumption].
        apply hB';split;[assumption|].
        setoid_rewrite <- Eγ.
        apply hom_Boxes,in_map_iff;exists β;tauto.
      + eapply (@hom_bij _ _ _ _ h).
      + simpl.
        eapply (@hom_Lbl _ _ _ _ h).
      + simpl.
        eapply (@hom_Ord _ _ _ _ h).
      + simpl;split;intros β Iβ.
        * apply in_map_iff in Iβ as (α&<-&Iα).
          apply hB' in Iα as (Iα&β&Iβ&E).
          exists β;tauto.
        * destruct (𝒫_spec (map (f ̃) β)) as (α&Iα&Eα).
          cut (α ∈ B').
          -- intros IB';exists (map f α);split.
             ++ apply in_map_iff;exists α;split;auto.
             ++ rewrite <- Eα,map_map.
                erewrite map_ext by apply inverse_elim2.
                rewrite map_id;reflexivity.
          -- apply hB';split;[assumption|].
             exists β;split;[assumption|].
             rewrite <- Eα,map_map.
             erewrite map_ext by apply inverse_elim2.
             rewrite map_id;reflexivity.
  Qed.

  
  Corollary subsumption_is_order_then_box :
    subsume ≃ order_subsumption ⋅ box_subsumption.
  Proof.
    intros p q;unfold prod,prod_Rel;simpl;split.
    - intros (f&Hf).
      apply Homomorphism_factorisation_1 in Hf as (r&g&h&Hh&Hg&_).
      exists r;split;[exists g|exists h];assumption.
    - intros (?&->&->);reflexivity.
  Qed.
  
  Proposition Homomorphism_factorisation_2 P Q f :
    homomorphism f -> exists R g h,
      order_homomorphism P R h
      /\ box_homomorphism R Q g
      /\ f ≃ g ∘ h.
  Proof.
    intros h.
    set (O := fun x y : ⌊P⌋ => f x ≤[Q] f y).
    assert (po_O: partialOrder O).
    - unfold O;split;intro;intros.
      + reflexivity.
      + etransitivity;eassumption.
      + cut (f x = f y);[apply is_injective|].
        apply antisymmetry;assumption.
    - exists (Build_Pomset (@ℓ _ P) po_O (@Pomset_hnil _ P));simpl.
      exists f,id;simpl.
      split;[split|split;[split|rewrite compose_id_r;reflexivity]].
      + apply bijective_id.
      + simpl;reflexivity.
      + unfold id,O;simpl.
        apply hom_Ord.
      + simpl.
        erewrite map_ext by apply map_id.
        rewrite map_id.
        reflexivity.
      + eapply (@hom_bij _ _ _ _ h).
      + simpl.
        eapply (@hom_Lbl _ _ _ _ h).
      + simpl.
        unfold O;reflexivity.
      + simpl;apply (@hom_Boxes _ _ _ _ h).
  Qed.

  Corollary subsumption_is_box_then_order :
    subsume ≃ box_subsumption ⋅ order_subsumption.
  Proof.
    intros p q;unfold prod,prod_Rel;simpl;split.
    - intros (f&Hf).
      apply Homomorphism_factorisation_2 in Hf as (r&g&h&Hh&Hg&_).
      exists r;split;[exists g|exists h];assumption.
    - intros (?&->&->);reflexivity.
  Qed.


  Lemma sub_pom_box (P Q: Pomset X) :
    Q ⊑b P <->
    exists B (I : B ∈ subsets (Boxes Q)),
      P ≃ (Build_Pomset (@ℓ _ Q) (@Pomset_po _ Q) (subsets_Boxes_hnil (subsets_In I))).
  Proof.
    split;simpl.
    - intros (f&hyp);simpl.
      destruct (@dec_prop_powerset_bnd _ (fun b => exists b', b' ∈ Boxes P /\ map f b' ≈ b)
                                       (Boxes Q)) as (B'&hB);
        [typeclasses eauto|].
      assert (I__B : B' ⊆ Boxes Q) by (intros x Ix;apply hB in Ix;tauto).
      apply subsets_spec in I__B as (B&I__B&E).
      setoid_rewrite E in hB;clear B' E.
      exists B,I__B;simpl;symmetry; exists f;split;try apply hyp.
      split.
      + intros b Ib;simpl in *.
        pose proof Ib as Ib'.
        apply (@box_Boxes _ _ _ hyp) in Ib' as (b'&Ib'&E).
        apply in_map_iff in Ib as (β&<-&Iβ).
        exists b';split;[|assumption].
        apply hB;split;[assumption|].
        exists β;tauto.
      + intros b Ib;simpl in *.
        apply hB in Ib as (Ib&β&Iβ&Eβ).
        exists (map f β);split;[apply in_map_iff;eauto|symmetry;assumption].
    - intros (B&IB&EB);symmetry in EB;destruct EB as (g&Ig);simpl in *.
      exists g;split;try apply Ig.
      rewrite (@iso_Boxes _ _ _ _ Ig);simpl.
      apply incl_smaller_sets,subsets_In,IB.
  Qed.

  Fixpoint less_boxes (s : bsp_terms X) : list (bsp_terms X) :=
    match s with
    | bsp_unit => [bsp_unit]
    | bsp_var x => [bsp_var x]
    | bsp_seq u v => lift_prod bsp_seq (less_boxes u) (less_boxes v)
    | bsp_par u v => lift_prod bsp_par (less_boxes u) (less_boxes v)
    | bsp_box u => less_boxes u ++ map bsp_box (less_boxes u)
    end.

  Lemma less_boxes_sem_spec s B (I : B ∈ subsets (Boxes ⟦s⟧)) :
    exists t, t ∈ less_boxes s /\ 
         ⟦t⟧ ≃ (Build_Pomset (@ℓ _ ⟦s⟧) (@Pomset_po _ ⟦s⟧)
                             (subsets_Boxes_hnil (subsets_In I))) .
  Proof.
    revert B I;induction s;rsimpl;intros B IB.
    - pose proof IB as I;apply subsets_app in I as (b1&b2&->&Ib1&Ib2).
      rewrite subsets_map in Ib1.
      rewrite subsets_map in Ib2.
      apply in_map_iff in Ib1 as (a1&<-&Ia1).
      apply in_map_iff in Ib2 as (a2&<-&Ia2).
      pose proof (IHs1 _ Ia1) as (t1&It1&Et1).
      pose proof (IHs2 _ Ia2) as (t2&It2&Et2).
      exists (t1 ⋅ t2);split.
      + apply lift_prod_spec;exists t1,t2;tauto.
      + rsimpl;rewrite Et1,Et2;clear Et1 Et2.
        simpl;exists id;simpl;split.
        * apply bijective_id.
        * simpl;reflexivity.
        * simpl;reflexivity.
        * simpl.
          erewrite map_ext by apply map_id.
          rewrite map_id.
          reflexivity.
    - pose proof IB as I;apply subsets_app in I as (b1&b2&->&Ib1&Ib2).
      rewrite subsets_map in Ib1.
      rewrite subsets_map in Ib2.
      apply in_map_iff in Ib1 as (a1&<-&Ia1).
      apply in_map_iff in Ib2 as (a2&<-&Ia2).
      pose proof (IHs1 _ Ia1) as (t1&It1&Et1).
      pose proof (IHs2 _ Ia2) as (t2&It2&Et2).
      exists (t1 ∥ t2);split.
      + apply lift_prod_spec;exists t1,t2;tauto.
      + rsimpl;rewrite Et1,Et2;clear Et1 Et2.
        simpl;exists id;simpl;split.
        * apply bijective_id.
        * simpl;reflexivity.
        * simpl;reflexivity.
        * simpl.
          erewrite map_ext by apply map_id.
          rewrite map_id.
          reflexivity.
    - destruct IB as [<-|F];[|tauto].
      exists (bsp_var x);simpl;split;[tauto|].
      exists id;split;simpl.
      + apply bijective_id.
      + simpl;reflexivity.
      + simpl;reflexivity.
      + simpl;reflexivity.
    - assert (B ∈ subsets (Boxes ⟦s⟧) \/ exists B', B = ⟨|s|⟩::B' /\ B' ∈ (subsets (Boxes ⟦s⟧)))
        as [IB'|(B'&->&IB')];try destruct (IHs _ IB') as (t&It&Et).
      + revert IB;clear.
        destruct ⟨|s|⟩;simpl.
        * intros [<-|F];[|tauto].
          left.
          pose proof (incl_nil (Boxes ⟦s⟧)) as I.
          apply subsets_spec in I as ([|x]&I&E);[assumption|].
          cut (x ∈ []);[simpl;tauto|].
          apply E;now left.
        * rewrite in_app_iff.
          intros [I|I];[|tauto].
          apply in_map_iff in I as (B'&<-&IB').
          right;exists B';tauto.
      + exists t;split;[apply in_app_iff;tauto|].
        rewrite Et;clear Et.
        exists id;split;simpl.
        * apply bijective_id.
        * simpl;reflexivity.
        * simpl;reflexivity.
        * simpl.
          erewrite map_ext by apply map_id.
          rewrite map_id.
          reflexivity.
      + exists (▢ t);split;[apply in_app_iff;right;apply in_map_iff;exists t;tauto|].
        rsimpl.
        rewrite Et;clear Et.
        exists id;split;simpl.
        * apply bijective_id.
        * simpl;reflexivity.
        * simpl;reflexivity.
        * simpl.
          rewrite map_id.
          erewrite map_ext by apply map_id.
          rewrite map_id.
          revert IB;clear.
          destruct ⟨|s|⟩;simpl.
          -- intros [F|F];inversion F.
          -- intros _;reflexivity.
    - destruct IB as [<-|F];[|tauto].
      exists bsp_unit;simpl;split;[tauto|].
      exists id;split;simpl.
      + apply bijective_id.
      + simpl;reflexivity.
      + simpl;reflexivity.
      + simpl;reflexivity.
  Qed.
  
  Lemma less_boxes_ax_spec s t :
    t ∈ less_boxes s -> s ⊑ t.
  Proof.
    revert t;induction s;intro t;rsimpl in *.
    - intro It;apply lift_prod_spec in It as (t1&t2&It1&It2&->).
      rewrite <- (IHs1 _ It1),<- (IHs2 _ It2).
      reflexivity.
    - intro It;apply lift_prod_spec in It as (t1&t2&It1&It2&->).
      rewrite <- (IHs1 _ It1),<- (IHs2 _ It2).
      reflexivity.
    - intros [<-|F];[reflexivity|tauto].
    - rewrite in_app_iff,in_map_iff;intros [I|(t'&<-&I)];apply IHs in I as <-;auto.
      apply bsp_subs_box_inf.
    - intros [<-|F];[reflexivity|tauto].
  Qed.

  Proposition completeness_box_hom s t : ⟦s⟧ ⊑b ⟦t⟧ -> s ⊑ t.
  Proof.
    intros If; apply sub_pom_box in If as (B&IB&EB).
    pose proof (less_boxes_sem_spec _ _ IB) as (t'&It'&Et').
    rewrite (less_boxes_ax_spec _ _ It').
    rewrite <- EB in Et'.
    apply completeness_bsp_terms_iso in Et' as ->;reflexivity.
  Qed.

  Section sub_pom_lift.
    Context {u v : Pomset X}.
    Context {f : ⌊u⌋ -> ⌊v⌋} {OHf : order_homomorphism u v f}.

    Global Instance map_f_bij : bijective (map f).
    Proof.
      split;split.
      - intros x;induction x as [|x0 x];intros [|y0 y];try discriminate||reflexivity.
        intro E';inversion E' as [[E0 E]];clear E'.
        apply IHx in E as ->.
        apply is_injective in E0 as ->.
        reflexivity.
      - intro y;induction y as [|y0 y].
        + exists [];reflexivity.
        + destruct IHy as (x&<-).
          destruct (@is_surjective _ _ f _ y0) as (x0&<-).
          exists (x0::x);reflexivity.
    Qed.

    Definition lift l x := proj1_sig (sub_pom_lift_fun u v l f x).

    Lemma lift_spec l x : 𝒯e (lift l x) = f (𝒯e x).
    Proof. unfold lift;destruct (sub_pom_lift_fun u v l f x);simpl;assumption. Qed.

    Instance lift_bij l : bijective (lift l).
    Proof.
      split;split.
      - intros x y E.
        cut (𝒯e (lift l x) = 𝒯e (lift l y));[|rewrite E;reflexivity].
        clear E;intro E;repeat rewrite lift_spec in E.
        repeat apply is_injective in E;assumption.
      - intros y.
        pose proof (sub_pom_T_internal y) as Iy.
        apply in_map_iff in Iy as (x'&Ex&Ix).
        apply sub_pom_T_invert in Ix as (x&<-).
        rewrite <- lift_spec in Ex.
        apply is_injective in Ex as <-.
        exists x;reflexivity.
    Qed.
    
    Lemma lift_hom l : order_homomorphism (u⇂l) (v⇂(map f l)) (lift l).
    Proof.
      split.
      - apply lift_bij.
      - intros x;simpl.
        rewrite lift_spec;simpl.
        apply order_Lbl.
      - intros x x';simpl;repeat rewrite lift_spec;apply order_Ord.
      - simpl;split;intros b Ib.
        + destruct (𝒫_spec b) as (a&IPb&Eb);exists a;split;[|assumption].
          apply sub_pom_box_spec;split;[assumption|].
          setoid_rewrite <- Eb;clear a IPb Eb.
          apply in_map_iff in Ib as (b'&<-&Ib').
          apply sub_pom_box_spec in Ib' as (_&b''&Ib''&E).
          assert (Ib : map f b'' ∈ map (map f) (Boxes u))
            by (apply in_map_iff;exists b'';tauto).
          apply (@order_Boxes _ _ _ OHf) in Ib as (a&Ia&Ea).
          rewrite E,map_map in Ea.
          exists a;split;[assumption|].
          rewrite <- Ea,map_map.
          erewrite map_ext;[reflexivity|].
          intro;symmetry;apply lift_spec.
        + apply sub_pom_box_spec in Ib as (_&b'&Ib'&Eb').
          apply OHf in Ib' as (a&Ia&Ea).
          apply in_map_iff in Ia as (a'&<-&Ia').
          rewrite Ea in Eb'.
          cut (exists a'', map (𝒯l {{l}}) a'' = a').
          * intros (a''&<-).
            destruct (𝒫_spec a'') as (a&Ia&E).
            exists (map (lift l) a);split.
            -- apply in_map_iff;exists a;split;[reflexivity|].
               apply sub_pom_box_spec;split;[assumption|].
               exists (map (𝒯l {{l}}) a'');split;[assumption|].
               rewrite E;reflexivity.
            -- rewrite <- E.
               clear a Ia E.
               clear b' Ea Ia'.
               rewrite map_map in Eb'.
               erewrite map_ext in Eb' by (intro;symmetry;apply lift_spec).
               intro x;split;intro I.
               ++ cut (𝒯e x ∈ map (𝒯l {{map f l}}) b);[|apply in_map_iff;exists x;tauto].
                  clear I;intro I;apply Eb',in_map_iff in I as (y&E&I).
                  apply is_injective in E as <- .
                  apply in_map_iff;exists y;tauto.
               ++ apply in_map_iff in I as (y&<-&I).
                  cut (𝒯e (lift l y) ∈ map (𝒯l {{map f l}}∘(lift l)) a'');
                    [|apply in_map_iff;exists y;tauto].
                  clear I;intro I;apply Eb',in_map_iff in I as (x&E&I).
                  apply is_injective in E as ->;assumption.
          * apply sub_pom_invert_list.
            intros a Ia.
            cut (f a ∈ map f a');[clear Ia;intro Ia|apply in_map_iff;exists a;tauto].
            apply Eb',in_map_iff in Ia as (x&E&Ix).
            destruct (@is_surjective _ _ (lift l) _ x) as (y&<-).
            rewrite lift_spec in E;apply is_injective in E as <- .
            apply sub_pom_T_internal.
    Qed.

    Lemma lift_compl l : ¬ (map f l) ≈ map f (¬ l).
    Proof.
      intro x.
      rewrite <- complement_spec.
      repeat rewrite in_map_iff.
      setoid_rewrite <- complement_spec.
      split.
      - intros F.
        destruct (@is_surjective _ _ f _ x) as (y&<-);exists y;split;[reflexivity|].
        intro I;apply F;exists y;tauto.
      - intros (y&<-&I) (y'&E&I').
        apply is_injective in E as ->.
        apply I,I'.
    Qed.
    Lemma lift_nested l : is_nested l <-> is_nested (map f l).
    Proof.
      unfold is_nested;split.
      - intros N b Ib.
        apply order_Boxes in Ib as (a&Ia&Ea).
        setoid_rewrite Ea;clear b Ea.
        apply in_map_iff in Ia as (b&<-&Ib).
        apply N in Ib as [h|h].
        + left;rewrite h;reflexivity.
        + right;intros e.
          destruct (@is_surjective _ _ f _ e) as (e'&<-).
          destruct (h e') as [Ie|Ie].
          * left;intro I;apply Ie.
            apply in_map_iff in I as (?&E&I).
            apply is_injective in E as ->;assumption.
          * right;intro I;apply Ie.
            apply in_map_iff in I as (?&E&I).
            apply is_injective in E as ->;assumption.
      - intros N b Ib.
        cut (map f b ∈ map (map f) (Boxes u));
          [clear Ib;intro Ib|apply in_map_iff;exists b;tauto].
        apply order_Boxes in Ib as (b'&Ib&E).
        apply N in Ib;setoid_rewrite <- E in Ib;clear b' E.
        destruct Ib as [Ib|Ib].
        + left.
          intros a Ia;cut (f a ∈ map f b);[clear Ia;intros Ia|apply in_map_iff;exists a;tauto].
          apply Ib,in_map_iff in Ia as (a'&E&Ia).
          apply is_injective in E as ->.
          assumption.
        + right;intros e.
          destruct (Ib (f e)) as [I|I].
          * left;intro I';apply I,in_map_iff;exists e;tauto.
          * right;intro I';apply I,in_map_iff;exists e;tauto.
    Qed.

    Lemma lift_prefix l : is_prefix l -> is_prefix (map f l).
    Proof.
      intros P e1 e2 I1 I2.
      apply in_map_iff in I1 as (x&<-&Ix).
      destruct (@is_surjective _ _ f _ e2) as (y&<-).
      apply order_Ord,P;[assumption|].
      intro I;apply I2,in_map_iff;exists y;tauto.
    Qed.

    Lemma lift_isolated l : is_isolated (map f l) -> is_isolated l.
    Proof.
      intros Is e1 e2 I1.
      cut (f e1 ∈ map f l);[clear I1;intros I1|apply in_map_iff;exists e1;tauto].
      intros O; cut (f e2 ∈ map f l).
      - intros h;apply in_map_iff in h as (x&E&Ix);apply is_injective in E as ->;assumption.
      - apply (Is (f e1) _ I1).
        destruct O as [O|O];apply order_Ord in O; tauto.
    Qed.
      
  End sub_pom_lift.
  
  Corollary lift_order u v f l :
    order_homomorphism u v f -> v⇂(map f l) ⊑o u⇂l.
  Proof. intros OHf;exists (lift l);apply lift_hom. Qed.
  
  Corollary lift_order_compl u v f l :
    order_homomorphism u v f -> v⇂(¬ (map f l)) ⊑o u⇂(¬ l).
  Proof.
    intro OHf.
    pose proof (@lift_compl u v f OHf l) as E.
    apply sub_pom_proper,order_subsumption_equiv in E.
    rewrite E.
    apply lift_order,OHf.
  Qed.
      
  Lemma seq_right_split_hom (s u v : bsp_terms X) :
    ⟦s⟧ ⊑o ⟦u⋅v⟧ -> exists l, s ≡ s ⨡ l ⋅ s ⨡(¬ l) /\ ⟦s⨡l⟧ ⊑o ⟦u⟧ /\ ⟦s⨡(¬ l)⟧ ⊑o ⟦v⟧.
  Proof.
    rsimpl;intros (f&hf).
    pose proof (@lift_hom _ _ _ hf (map inl ⟨|u|⟩)) as OHf.
    exists (map f (map inl ⟨| u |⟩));split;[|split].
    - apply sub_term_split_seq.
      + apply lift_prefix.
        intros x1 x2 I1 I2.
        apply in_map_iff in I1 as (e1&<-&_).
        destruct x2 as [e2|e2];simpl;[|tauto].
        exfalso;apply I2,in_map_iff;exists e2;split;[reflexivity|apply domain_spec].
      + rewrite <- lift_nested.
        intros b Ib.
        simpl in Ib;apply in_app_iff in Ib as [Ib|Ib];apply in_map_iff in Ib as (b'&<-&Ib').
        * left;intros e Ie;apply in_map_iff.
          apply in_map_iff in Ie as (e'&<-&Ie').
          exists e';split;[reflexivity|apply domain_spec].
        * right;intros [e|e].
          -- left;intros I.
             apply in_map_iff in I as (y&E&_);discriminate.
          -- right;intros I.
             apply in_map_iff in I as (y&E&_);discriminate.
    - rewrite (order_subsumption_equiv _ _ (sub_term_sub_pom _ _)).
      etransitivity;[eapply lift_order,hf|].
      apply order_subsumption_equiv.
      transitivity ⟦(u⋅v)⨡map inl ⟨|u|⟩⟧;[rewrite sub_term_sub_pom;reflexivity|].
      simpl.
      apply soundness_bsp_terms;rsimpl.
      unfold bsp_get_seq_right;rewrite seq_proj_get_seq_l_r,sub_term_nil.
      unfold bsp_get_seq_left;rewrite <- seq_proj_get_seq_l,sub_term_full.
      apply right_unit.
    - rewrite (order_subsumption_equiv _ _ (sub_term_sub_pom _ _)).
      etransitivity;[eapply lift_order_compl,hf|].
      apply order_subsumption_equiv.
      transitivity ⟦(u⋅v)⨡¬ (map inl ⟨|u|⟩ : list ⌊|u⋅v|⌋)⟧;
        [rewrite sub_term_sub_pom;reflexivity|].
      simpl.
      apply soundness_bsp_terms;rsimpl.
      erewrite sub_term_proper,sub_term_nil,sub_term_proper,sub_term_full;
        [apply left_unit| |].
      + intros x;split;[intro;apply domain_spec|].
        intros _;apply get_seq_right_spec.
        apply filter_In;split;[apply domain_spec|].
        apply negb_true_iff,inb_false.
        intros I;apply in_map_iff in I as (?&E&_);discriminate.
      + intros x;split;[|simpl;tauto].
        intros I;apply get_seq_left_spec in I.
        unfold complement in I.
        apply filter_In in I as (_&I). 
        apply negb_true_iff,inb_false in I.
        simpl;apply I,in_map_iff;exists x;split;[reflexivity|apply domain_spec].
  Qed.

  Lemma par_left_split_hom (s u v : bsp_terms X) :
    ⟦u ∥ v⟧ ⊑o ⟦s⟧ -> exists l, s ≡ s ⨡ l ∥ s ⨡(¬ l) /\ ⟦u⟧ ⊑o ⟦s⨡l⟧ /\ ⟦v⟧ ⊑o ⟦s⨡(¬ l)⟧.
  Proof.
    rsimpl.
    intros (f&hf).
    destruct (@is_surjective _ _ (map f) (@bij_surjective _ _ _ map_f_bij)
                             (map inl ⟨| u |⟩)) as (m&Em).
    exists m;split;[|split].
    - apply sub_term_split_par.
      + apply lift_isolated;rewrite Em.
        intros f1 f2 I1 O;apply in_map_iff in I1 as (e1&<-&_).
        destruct f2 as [e2|e2];[|simpl in O;tauto].
        apply in_map_iff;exists e2;split;[reflexivity|].
        apply domain_spec.
      + apply lift_nested;rewrite Em.
        intros b Ib;simpl in Ib.
        apply in_app_iff in Ib as [Ib|Ib];apply in_map_iff in Ib as (b'&<-&Ib').
        * left;rewrite domain_incl;reflexivity.
        * right;intros [e|e].
          -- left;intros Ix;apply in_map_iff in Ix as (x&F&_);discriminate.
          -- right;intros Ix;apply in_map_iff in Ix as (x&F&_);discriminate.
    - etransitivity;[|apply order_subsumption_equiv;symmetry;apply sub_term_sub_pom].
      etransitivity;[|eapply lift_order,hf].
      apply order_subsumption_equiv.
      transitivity ⟦(u∥v)⨡(map f m)⟧;[|rewrite sub_term_sub_pom;reflexivity].
      rewrite Em;clear m Em;simpl.
      apply soundness_bsp_terms;rsimpl.
      unfold bsp_get_par_right;rewrite par_proj_get_par_l_r,sub_term_nil.
      unfold bsp_get_par_left;rewrite <- par_proj_get_par_l,sub_term_full.
      symmetry;apply right_unit.
    - etransitivity;[|apply order_subsumption_equiv;symmetry;apply sub_term_sub_pom].
      etransitivity;[|eapply lift_order_compl,hf].
      apply order_subsumption_equiv.
      transitivity ⟦(u∥v)⨡¬(map f m)⟧;[|rewrite sub_term_sub_pom;reflexivity].
      rewrite Em;clear m Em;simpl.
      simpl.
      apply soundness_bsp_terms;rsimpl.
      erewrite sub_term_proper,sub_term_nil,sub_term_proper,sub_term_full;
        [symmetry;apply left_unit| |].
      + intros x;split;[intro;apply domain_spec|].
        intros _;apply get_par_right_spec.
        apply filter_In;split;[apply domain_spec|].
        apply negb_true_iff,inb_false.
        intros I;apply in_map_iff in I as (?&E&_);discriminate.
      + intros x;split;[|simpl;tauto].
        intros I;apply get_par_left_spec in I.
        unfold complement in I.
        apply filter_In in I as (_&I). 
        apply negb_true_iff,inb_false in I.
        simpl;apply I,in_map_iff;exists x;split;[reflexivity|apply domain_spec].
  Qed.

  Lemma bsp_clean_box_no_full_box (b : bsp_terms X) :
    is_bsp_clean (bsp_box b) ->
    ~ ([⟨| b |⟩] ≲ Boxes ⟦ b ⟧).
  Proof.
    intros C F;assert (C' : is_bsp_clean b) by (destruct b;apply C||(exfalso;apply C)).
    assert (I: ⟨| b |⟩∈ [⟨| b |⟩]) by now left.
    apply F in I as (b'&Ib'&E).
    clear F.
    destruct b.
    - destruct C' as (C1&C2).
      simpl in *;apply in_app_iff in Ib' as [Ib|Ib];
        apply in_map_iff in Ib as (b&<-&Ib).
      + apply bsp_clean_get_elt in C2 as e.
        cut (inr e ∈ map inl b).
        * intro Ix;apply in_map_iff in Ix as (x&F&_).
          discriminate.
        * apply E,in_app_iff;right;apply in_map_iff;exists e;
            split;[reflexivity|apply domain_spec].
      + apply bsp_clean_get_elt in C1 as e.
        cut (inl e ∈ map inr b).
        * intro Ix;apply in_map_iff in Ix as (x&F&_).
          discriminate.
        * apply E,in_app_iff;left;apply in_map_iff;exists e;
            split;[reflexivity|apply domain_spec].
    - destruct C' as (C1&C2).
      simpl in *;apply in_app_iff in Ib' as [Ib|Ib];
        apply in_map_iff in Ib as (b&<-&Ib).
      + apply bsp_clean_get_elt in C2 as e.
        cut (inr e ∈ map inl b).
        * intro Ix;apply in_map_iff in Ix as (x&F&_).
          discriminate.
        * apply E,in_app_iff;right;apply in_map_iff;exists e;
            split;[reflexivity|apply domain_spec].
      + apply bsp_clean_get_elt in C1 as e.
        cut (inl e ∈ map inr b).
        * intro Ix;apply in_map_iff in Ix as (x&F&_).
          discriminate.
        * apply E,in_app_iff;left;apply in_map_iff;exists e;
            split;[reflexivity|apply domain_spec].
    - apply Ib'.
    - apply C.
    - apply Ib'.
  Qed.
  
  Lemma box_left_split_hom (s t : bsp_terms X) :
    is_bsp_clean (▢ s) -> is_bsp_clean t -> ⟦▢ s⟧ ⊑o ⟦t⟧ -> exists v, t = ▢ v /\ ⟦s⟧ ⊑o ⟦v⟧.
  Proof.
    intros Cs C;destruct t as [ | | |b|].
    + destruct C as (C1&C2);intros F;exfalso.
      cut (⟨|▢s|⟩ ∈ Boxes ⟦ ▢ s ⟧).
      * intros Ib.
        destruct F as (f&hf).
        apply (@order_Boxes _ _ f hf) in Ib as (b&Ib&Eb).
        simpl in Ib;rewrite map_app,in_app_iff,map_map,map_map in Ib.
        destruct Ib as [Ib|Ib];apply in_map_iff in Ib as (b'&<-&Ib).
        -- apply bsp_clean_get_elt in C2 as e.
           assert (I: f (inr e) ∈ ⟨|▢ s|⟩) by apply domain_spec.
           apply Eb,in_map_iff in I as (x&E&Ix).
           pose proof (@order_bij _ _ _ hf) as B.
           apply is_injective in E as ->.
           apply in_map_iff in Ix as (?&F&_);discriminate.
        -- apply bsp_clean_get_elt in C1 as e.
           assert (I: f (inl e) ∈ ⟨|▢ s|⟩) by apply domain_spec.
           apply Eb,in_map_iff in I as (x&E&Ix).
           pose proof (@order_bij _ _ _ hf) as B.
           apply is_injective in E as ->.
           apply in_map_iff in Ix as (?&F&_);discriminate.
      * destruct (Boxes_box_spec ⟦s⟧) as [h|h].
        -- exfalso.
           apply order_subsumption_smaller in F.
           apply is_bsp_clean_bsp_size in C1.
           apply is_bsp_clean_bsp_size in C2.
           apply sizePomset_subsumption in F.
           apply sizePomset_equiv in h.
           rewrite <- interpret_bsp_size in F,h,F.
           rsimpl in *.
           rewrite h in F.
           unfold un,unPomsets,size at 1,sizePomset in F;simpl in F.
           rewrite size_leaf_false in F;lia.
        -- rsimpl in *;rewrite h;now left.
    + destruct C as (C1&C2);intros F;exfalso.
      cut (⟨|▢s|⟩ ∈ Boxes ⟦ ▢ s ⟧).
      * intros Ib.
        destruct F as (f&hf).
        apply (@order_Boxes _ _ f hf) in Ib as (b&Ib&Eb).
        simpl in Ib;rewrite map_app,in_app_iff,map_map,map_map in Ib.
        destruct Ib as [Ib|Ib];apply in_map_iff in Ib as (b'&<-&Ib).
        -- apply bsp_clean_get_elt in C2 as e.
           assert (I: f (inr e) ∈ ⟨|▢ s|⟩) by apply domain_spec.
           apply Eb,in_map_iff in I as (x&E&Ix).
           pose proof (@order_bij _ _ _ hf) as B.
           apply is_injective in E as ->.
           apply in_map_iff in Ix as (?&F&_);discriminate.
        -- apply bsp_clean_get_elt in C1 as e.
           assert (I: f (inl e) ∈ ⟨|▢ s|⟩) by apply domain_spec.
           apply Eb,in_map_iff in I as (x&E&Ix).
           pose proof (@order_bij _ _ _ hf) as B.
           apply is_injective in E as ->.
           apply in_map_iff in Ix as (?&F&_);discriminate.
      * destruct (Boxes_box_spec ⟦s⟧) as [h|h].
        -- exfalso.
           apply order_subsumption_smaller in F.
           apply is_bsp_clean_bsp_size in C1.
           apply is_bsp_clean_bsp_size in C2.
           apply sizePomset_subsumption in F.
           apply sizePomset_equiv in h.
           rewrite <- interpret_bsp_size in F,h,F.
           rsimpl in *.
           rewrite h in F.
           unfold un,unPomsets,size at 1,sizePomset in F;simpl in F.
           rewrite size_leaf_false in F;lia.
        -- rsimpl in *;rewrite h;now left.
    + clear C;intros F;exfalso.
      cut (⟨|▢s|⟩ ∈ Boxes ⟦ ▢ s ⟧).
      * intros Ib.
        destruct F as (f&hf).
        apply (@order_Boxes _ _ f hf) in Ib as (b&Ib&Eb).
        simpl in Ib;tauto.
      * destruct (Boxes_box_spec ⟦s⟧) as [h|h].
        -- exfalso.
           apply order_subsumption_smaller in F.
           apply sizePomset_subsumption in F.
           apply sizePomset_equiv in h.
           rewrite <- interpret_bsp_size in F,h,F.
           rsimpl in *.
           rewrite h in F.
           unfold un,unPomsets,size at 1,sizePomset in F;simpl in F.
           rewrite size_leaf_false in F;lia.
        -- rsimpl in *;rewrite h;now left.
    + rsimpl.
      intros h.
      exists b;split;[reflexivity|].
        rewrite <- (interpret_bsp_box b) in h.
        pose proof h as (f&hf).
        exists f;split;try apply hf.
        pose proof (@order_Boxes _ _ _ hf) as E.
        assert (C' : is_bsp_clean b) by (destruct b;apply C||(exfalso;apply C)).
        rewrite (bsp_get_box_Boxes C') in E.
        revert E.
        destruct (Boxes_box_spec ⟦s⟧) as [h'| ->].
        -- exfalso.
           apply order_subsumption_smaller in h.
           rewrite h',Pomset_box_unit,<-interpret_bsp_unit in h.
           apply sizePomset_subsumption in h.
           repeat rewrite <- interpret_bsp_size in h.
           apply is_bsp_clean_bsp_size in C.
           rsimpl in *;lia.
        -- rsimpl.
           replace ⟪ PomType (sem_bsp b) ⟫
             with ⟨|b|⟩ by reflexivity.
           unfold bsp_get_box.
           rewrite (@map_ext _ _ (map id) id),map_id  by apply map_id.
           intro E;split;intros x Ix.
           ++ cut (exists b0 : list ⌊| s |⌋, b0 ∈ (⟨| s |⟩ ::  Boxes ⟦ s ⟧) /\ x ≈ b0).
              ** intros (b0&[<-|Ib0]&Eb0).
                 --- cut ([⟨| b |⟩] ≲ Boxes ⟦ b ⟧).
                     +++ intro F;exfalso;revert F;apply bsp_clean_box_no_full_box,C.
                     +++ apply in_map_iff in Ix as (y&<-&Iy).
                         intros ? [<-|F];[|exfalso;apply F].
                         exists y;split;[assumption|].
                         apply domain_equiv.
                         intros e _.
                         cut (f e ∈ map f y).
                         *** intros I;apply in_map_iff in I as (?&EE&I).
                             apply is_injective in EE as ->;assumption.
                         *** apply Eb0,domain_spec.
                 --- exists b0;tauto.
              ** apply E;now right.
           ++ pose proof Ix as I.
              cut (x ∈ (⟨|s|⟩::Boxes ⟦s⟧));[|now right].
              clear Ix;intro Ix;apply E in Ix as (y&[<-|Iy]&Ey).
              ** exfalso.
                 apply (bsp_clean_box_no_full_box _ Cs).
                 intros ? [<-|F];[|exfalso;apply F].
                 exists x;split;[assumption|].
                 rewrite Ey.
                 apply domain_equiv.
                 intros e _.
                 destruct (@is_surjective _ _ f _ e) as (y&<-).
                 apply in_map_iff;exists y;split;[reflexivity|apply domain_spec].
              ** exists y;tauto.
    + exfalso;apply C.   
  Qed.

  Lemma box_right_split_hom (s t : bsp_terms X) :
    is_bsp_clean s -> is_bsp_clean (▢ t) -> ⟦s⟧ ⊑o ⟦▢ t⟧ -> exists v, s ≡ ▢ v /\ ⟦v⟧ ⊑o ⟦t⟧.
  Proof.
    intros C Ct E.
    destruct s.
    + exfalso.
      destruct (Boxes_box_spec ⟦t⟧) as [F|F].
      * apply order_subsumption_smaller in E;
          rewrite interpret_bsp_box,F,Pomset_box_unit,<-interpret_bsp_unit in E.
        apply sizePomset_subsumption in E.
        destruct C as (C1&C2).
        apply is_bsp_clean_bsp_size in C1.
        repeat rewrite <- interpret_bsp_size in E.
        rsimpl in E;lia.
      * rsimpl in E;destruct E as (f&hf).
        destruct C as (C1&C2).
        pose proof (@order_Boxes _ _ f _) as (E&_).
        set (l := map f ⟪PomType (▢ ⟦t⟧)⟫).
        assert (I: l ∈ (map (map f) (Boxes (▢ ⟦ t ⟧))))
          by (rewrite F;now left).
        apply E in I as (b&Ib&Eb).
        apply in_app_iff in Ib as [Ib|Ib];apply in_map_iff in Ib as (b'&<-&Ib).
        -- apply bsp_clean_get_elt in C2 as e.
           pose proof (@order_bij _ _ _ hf) as B.
           destruct (@is_surjective _ _ f _ (inr e)) as (x&Ex).
           assert (I: f x ∈ l)
             by (apply in_map_iff;exists x;split;[reflexivity|apply domain_spec]).
           apply Eb in I;rewrite Ex in I;apply in_map_iff in I as (?&?&_).
           discriminate.
        -- apply bsp_clean_get_elt in C1 as e.
           pose proof (@order_bij _ _ _ hf) as B.
           destruct (@is_surjective _ _ f _ (inl e)) as (x&Ex).
           assert (I: f x ∈ l)
             by (apply in_map_iff;exists x;split;[reflexivity|apply domain_spec]).
           apply Eb in I;rewrite Ex in I;apply in_map_iff in I as (?&?&_).
           discriminate.
    + exfalso.
      destruct (Boxes_box_spec ⟦t⟧) as [F|F].
      * apply order_subsumption_smaller in E;
          rewrite interpret_bsp_box,F,Pomset_box_unit,<-interpret_bsp_unit in E.
        apply sizePomset_subsumption in E.
        destruct C as (C1&C2).
        apply is_bsp_clean_bsp_size in C1.
        repeat rewrite <- interpret_bsp_size in E.
        rsimpl in E;lia.
      * rsimpl in E;destruct E as (f&hf).
        destruct C as (C1&C2).
        pose proof (@order_Boxes _ _ f _) as (E&_).
        set (l := map f ⟪PomType (▢ ⟦t⟧)⟫).
        assert (I: l ∈ (map (map f) (Boxes (▢ ⟦ t ⟧))))
          by (rewrite F;now left).
        apply E in I as (b&Ib&Eb).
        apply in_app_iff in Ib as [Ib|Ib];apply in_map_iff in Ib as (b'&<-&Ib).
        -- apply bsp_clean_get_elt in C2 as e.
           pose proof (@order_bij _ _ _ hf) as B.
           destruct (@is_surjective _ _ f _ (inr e)) as (x&Ex).
           assert (I: f x ∈ l)
             by (apply in_map_iff;exists x;split;[reflexivity|apply domain_spec]).
           apply Eb in I;rewrite Ex in I;apply in_map_iff in I as (?&?&_).
           discriminate.
        -- apply bsp_clean_get_elt in C1 as e.
           pose proof (@order_bij _ _ _ hf) as B.
           destruct (@is_surjective _ _ f _ (inl e)) as (x&Ex).
           assert (I: f x ∈ l)
             by (apply in_map_iff;exists x;split;[reflexivity|apply domain_spec]).
           apply Eb in I;rewrite Ex in I;apply in_map_iff in I as (?&?&_).
           discriminate.
    + exfalso.
      destruct (Boxes_box_spec ⟦t⟧) as [F|F].
      * apply order_subsumption_smaller in E;
          rewrite interpret_bsp_box,F,Pomset_box_unit,<-interpret_bsp_unit in E.
        apply sizePomset_subsumption in E.
        repeat rewrite <- interpret_bsp_size in E.
        rsimpl in E;lia.
      * rsimpl in E;destruct E as (f&hf).
        pose proof (@order_Boxes _ _ f _) as (E&_).
        set (l := map f ⟪PomType (▢ ⟦t⟧)⟫).
        assert (I: l ∈ (map (map f) (Boxes (▢ ⟦ t ⟧))))
          by (rewrite F;now left).
        apply E in I as (b&Ib&_);apply Ib.
    + exists s.
      split;[reflexivity|].
      replace (bsp_box s) with (box s) in * by reflexivity.
      apply box_left_split_hom in E as (t'&E&h);try assumption.
      inversion E;subst;assumption.
    + exfalso;apply C.
  Qed.

  Lemma var_split_hom s a : ⟦s⟧ ⊑o ⟦bsp_var a⟧ \/ ⟦bsp_var a⟧ ⊑o ⟦s⟧ -> s ≡ bsp_var a.
  Proof.
    intros [E|E].
    - destruct (@size_1_eq_atomic _ ⟦s⟧) as (b&[Eb|F]).
      + apply order_subsumption_smaller,sizePomset_subsumption in E.
        rewrite E;reflexivity.
      + apply order_subsumption_smaller in E.
        rewrite Eb in E.
        replace (AtomicPomset b) with ⟦bsp_var b⟧ in * by reflexivity.
        apply completeness_bsp_terms_iso in Eb;rewrite Eb;clear s Eb.
        replace b with a;[reflexivity|].
        destruct E as (f&hf).
        cut (ℓ (υ : ⌊|bsp_var a|⌋) = ℓ (f (υ : ⌊|bsp_var a|⌋))).
        * simpl;tauto.
        * symmetry;apply hom_Lbl.
      + exfalso.
        symmetry in F;apply order_subsumption_equiv in F;rewrite <- F in E.
        clear s F.
        destruct E as (f&hf).
        pose proof (@order_Boxes _ _ f hf) as (_&E).
        assert (F: [υ] ∈ Boxes (▢ (AtomicPomset b))) by now left.
        apply E in F as (x&I&_).
        apply in_map_iff in I as (?&_&I).
        apply I.
    - destruct (@size_1_eq_atomic _ ⟦s⟧) as (b&[Eb|F]).
      + apply order_subsumption_smaller,sizePomset_subsumption in E.
        rewrite <- E;reflexivity.
      + apply order_subsumption_smaller in E.
        rewrite Eb in E.
        replace (AtomicPomset b) with ⟦bsp_var b⟧ in * by reflexivity.
        apply completeness_bsp_terms_iso in Eb;rewrite Eb;clear s Eb.
        replace b with a;[reflexivity|].
        destruct E as (f&hf).
        cut (ℓ (υ : ⌊|bsp_var b|⌋) = ℓ (f (υ : ⌊|bsp_var b|⌋))).
        * simpl;intros ->;reflexivity.
        * symmetry;apply hom_Lbl.
      + exfalso.
        apply order_subsumption_equiv in F;rewrite F in E.
        clear s F.
        destruct E as (f&hf).
        pose proof (@order_Boxes _ _ f hf) as (E&_).
        assert (F: [f υ] ∈ map (map f) (Boxes (▢ (AtomicPomset b)))) by now left.
        apply E in F as (x&I&_);apply I.
  Qed.
        
  Lemma unit_split_hom s : ⟦s⟧ ⊑o ⟦𝟭⟧ \/ ⟦𝟭⟧ ⊑o ⟦s⟧ -> s ≡ 𝟭.
  Proof.
    intros E;apply bsp_size_unit.
    destruct E as [E|E];apply order_subsumption_smaller,sizePomset_subsumption in E;
      repeat rewrite <- interpret_bsp_size in E;rewrite E||rewrite <- E;reflexivity.
  Qed.

  (*** to be moved *)
  (*** map_bij *)

  Global Instance map_bijective {A B} (f : A -> B) :
    bijective f -> bijective (map f).
  Proof.
    split;split.
    - intros x;induction x as [|x0 x];intros [|y0 y];try discriminate||reflexivity.
      intro E';inversion E' as [[E0 E]];clear E'.
      apply IHx in E as ->.
      apply is_injective in E0 as ->.
      reflexivity.
    - intro y;induction y as [|y0 y].
      + exists [];reflexivity.
      + destruct IHy as (x&<-).
        destruct (@is_surjective _ _ f _ y0) as (x0&<-).
        exists (x0::x);reflexivity.
  Qed.
  (*** complement *)

  Section compl.
    Context {t : bintree}.

    Lemma complement_involutive (l : list ⟨t⟩) : ¬(¬l) ≈ l.
    Proof. intro x;repeat rewrite <- complement_spec;case_in x l;tauto. Qed.

    Global Instance complement_proper :
      Proper (@equivalent _ ==> @equivalent _) (@complement t).
    Proof. intros l m E x;repeat rewrite <- complement_spec;rewrite E;tauto. Qed.
    Global Instance complement_proper_incl :
      Proper (@incl _ ==> Basics.flip (@incl _)) (@complement t).
    Proof. intros l m E x;repeat rewrite <- complement_spec;rewrite E;tauto. Qed.
    

  End compl.

  (*** intersection *)

  Section intersection.
    Context {t : bintree}.

    Definition intersection (l m : list ⟨t⟩) := (fun x => inb x l):> m.

    Infix " ∩ " := intersection (at level 40).
    
    Lemma intersection_spec l m x : x ∈ l ∩ m <-> x ∈ l /\ x ∈ m.
    Proof. unfold intersection;rewrite filter_In,inb_spec;tauto. Qed.

    Global Instance intersection_equivalent :
      Proper (@equivalent _ ==> @equivalent _ ==> @equivalent _) intersection.
    Proof. intros ? ? El ? ? Em ?;repeat rewrite intersection_spec;rewrite El,Em;tauto. Qed.

    Global Instance intersection_incl :
      Proper (@incl _ ==> @incl _ ==> @incl _) intersection.
    Proof. intros ? ? El ? ? Em ?;repeat rewrite intersection_spec;rewrite El,Em;tauto. Qed.

    Lemma de_morgan_inter l m : ¬ (l∩m) ≈ ¬l ++ ¬ m.
    Proof.
      intro x;
        repeat rewrite intersection_spec || rewrite in_app_iff || rewrite <- complement_spec.
      case_in x l;case_in x m;tauto.
    Qed.
    Lemma de_morgan_app l m : ¬ (l++m) ≈ ¬l ∩ ¬ m.
    Proof.
      intro x;
        repeat rewrite intersection_spec || rewrite in_app_iff || rewrite <- complement_spec.
      case_in x l;case_in x m;tauto.
    Qed.

    Lemma inter_comm l m : l ∩ m ≈ m ∩ l.
    Proof. intro ;repeat rewrite intersection_spec;tauto. Qed.

    Lemma inter_idem l : l ∩ l ≈ l.
    Proof. intro ;repeat rewrite intersection_spec;tauto. Qed.

    Lemma inter_top l : l ∩ ⟪t⟫ ≈ l.
    Proof. intro x;pose proof (domain_spec x);rewrite intersection_spec;tauto. Qed.
    
    Lemma inter_nil l : l ∩ [] ≈ [].
    Proof. intro x;rewrite intersection_spec;simpl;tauto. Qed.    
  End intersection.
  Infix " ∩ " := intersection (at level 40).

  (*** end move *)

  Section seq_par_split_hom.
    Section par_stuff.
      Context {u v : Pomset X}.
      Definition U : list ⌊ u ∥ v ⌋ := map inl ⟪PomType u⟫.
      Definition V : list ⌊ u ∥ v ⌋ := map inr ⟪PomType v⟫.

      Remark U_spec e : e ∈ U <-> exists e' : ⌊u⌋ , e = inl e'.
      Proof.
        unfold U;rewrite in_map_iff;split.
        - intros (e'&<-&_);exists e';tauto.
        - intros (e'&->);exists e';split;[reflexivity|apply domain_spec].
      Qed.
      Remark V_spec e : e ∈ V <-> exists e' : ⌊v⌋ , e = inr e'.
      Proof.
        unfold V;rewrite in_map_iff;split.
        - intros (e'&<-&_);exists e';tauto.
        - intros (e'&->);exists e';split;[reflexivity|apply domain_spec].
      Qed.
      Lemma u_project l : (u∥v) ⇂ (U ∩ l) ≃ u ⇂ (get_par_left l).
      Proof.
        destruct (sub_pom_make_fun u (u∥v) (get_par_left l) (U∩l) inl)
          as (f&hf).
        - intros x Ix.
          apply in_map_iff in Ix as (y&<-&Iy).
          apply get_par_left_spec in Iy.
          apply intersection_spec;split;[|assumption].
          apply in_map_iff;exists y;split;[reflexivity|apply domain_spec].
        - exists f;split.
          + split;split.
            * intros x y E.
              cut ((inl (𝒯e x) : ⌊ u∥v ⌋)= inl (𝒯e y)).
              -- intro E';inversion E' as [E''].
                 revert E''; apply is_injective.
              -- repeat rewrite <- hf;rewrite E;reflexivity.
            * intros y.
              pose proof (sub_pom_T_internal y) as Iy.
              apply intersection_spec in Iy as (Ix&Iy).
              apply U_spec in Ix as (x&E).
              rewrite E in Iy.
              apply get_par_left_spec,sub_pom_T_invert in Iy as (x'&<-).
              rewrite <- hf in E.
              apply is_injective in E as ->.
              exists x';reflexivity.
          + intro a.
            transitivity (ℓ (𝒯e (f a))).
            * reflexivity.
            * rewrite hf;reflexivity.
          + intros a a'.
            transitivity (inl (𝒯e a) ≤[u∥v] inl (𝒯e a'));[reflexivity|].
            repeat rewrite <- hf;reflexivity.
          + split;intros b;setoid_rewrite in_map_iff;
              setoid_rewrite sub_pom_Boxes.
            * intros (B&<-&_&B'&IB'&E).
              destruct (𝒫_spec (map f B)) as (B''&IB''&EB'').
              exists B'';split;[split;[assumption|]|assumption].
              exists (map inl B');split.
              -- simpl;apply in_app_iff;left;apply in_map_iff;exists B';tauto.
              -- rewrite <- EB'',E.
                 repeat rewrite map_map.
                 symmetry;erewrite map_ext by apply hf;reflexivity.
            * intros (_&B&IB&EB).
              simpl in IB;apply in_app_iff in IB as [IB|IB];
                apply in_map_iff in IB as (B'&<-&IB').
              -- destruct (@sub_pom_invert_list _ _ (get_par_left l) B') as (B''&<-).
                 ++ intros e Ie;apply get_par_left_spec.
                    cut ((inl e : ⌊ u ∥ v ⌋) ∈ map inl B');[|apply in_map_iff;exists e;tauto].
                    rewrite EB;intros I;apply in_map_iff in I as (x&<-&_).
                    pose proof (sub_pom_T_internal x) as Ix.
                    apply intersection_spec in Ix;tauto.
                 ++ erewrite map_map, <- map_ext,<-map_map in EB by apply hf.
                    destruct (𝒫_spec B'') as (B&IB&EB').
                    exists (map f B);split.
                    ** exists B;split;[reflexivity|split;[assumption|]].
                       exists (map (fun e => 𝒯e e) B'');split;[assumption|].
                       rewrite EB';reflexivity.
                    ** rewrite <- EB'.
                       intro e;transitivity (𝒯e e ∈ map (fun e => 𝒯e e) b).
                       --- rewrite in_map_iff.
                           split;[intro I;exists e;tauto|].
                           intros (x&E&Ix);apply is_injective in E as ->;assumption.
                       --- rewrite <- EB;symmetry.
                           rewrite (in_map_iff _ _ (𝒯e e)).
                           split;[intro I;exists e;tauto|].
                           intros (x&E&Ix);apply is_injective in E as ->;assumption.
              -- exfalso.
                 destruct B' as [|e B'].
                 ++ eapply Pomset_hnil,IB'.
                 ++ cut (inr e ∈ map (𝒯l {{U ∩ l}}) b).
                    ** intro I;apply in_map_iff in I as (e'&E&_).
                       pose proof (sub_pom_T_internal e') as Ie'.
                       apply intersection_spec in Ie' as (Ie'&_).
                       apply U_spec in Ie' as (x&Ex).
                       rewrite E in Ex;discriminate.
                    ** apply EB;now left.
      Qed.
      
      Lemma v_project l : (u∥v) ⇂ (V ∩ l) ≃ v ⇂ (get_par_right l).
      Proof.
        destruct (sub_pom_make_fun v (u∥v) (get_par_right l) (V∩l) inr)
          as (f&hf).
        - intros x Ix.
          apply in_map_iff in Ix as (y&<-&Iy).
          apply get_par_right_spec in Iy.
          apply intersection_spec;split;[|assumption].
          apply in_map_iff;exists y;split;[reflexivity|apply domain_spec].
        - exists f;split.
          + split;split.
            * intros x y E.
              cut ((inr (𝒯e x) : ⌊ u∥v ⌋)= inr (𝒯e y)).
              -- intro E';inversion E' as [E''].
                 revert E''; apply is_injective.
              -- repeat rewrite <- hf;rewrite E;reflexivity.
            * intros y.
              pose proof (sub_pom_T_internal y) as Iy.
              apply intersection_spec in Iy as (Ix&Iy).
              apply V_spec in Ix as (x&E).
              rewrite E in Iy.
              apply get_par_right_spec,sub_pom_T_invert in Iy as (x'&<-).
              rewrite <- hf in E.
              apply is_injective in E as ->.
              exists x';reflexivity.
          + intro a.
            transitivity (ℓ (𝒯e (f a))).
            * reflexivity.
            * rewrite hf;reflexivity.
          + intros a a'.
            transitivity (inr (𝒯e a) ≤[u∥v] inr (𝒯e a'));[reflexivity|].
            repeat rewrite <- hf;reflexivity.
          + split;intros b;setoid_rewrite in_map_iff;
              setoid_rewrite sub_pom_Boxes.
            * intros (B&<-&_&B'&IB'&E).
              destruct (𝒫_spec (map f B)) as (B''&IB''&EB'').
              exists B'';split;[split;[assumption|]|assumption].
              exists (map inr B');split.
              -- simpl;apply in_app_iff;right;apply in_map_iff;exists B';tauto.
              -- rewrite <- EB'',E.
                 repeat rewrite map_map.
                 symmetry;erewrite map_ext by apply hf;reflexivity.
            * intros (_&B&IB&EB).
              simpl in IB;apply in_app_iff in IB as [IB|IB];
                apply in_map_iff in IB as (B'&<-&IB').
              -- exfalso.
                 destruct B' as [|e B'].
                 ++ eapply Pomset_hnil,IB'.
                 ++ cut (inl e ∈ map (𝒯l {{V ∩ l}}) b).
                    ** intro I;apply in_map_iff in I as (e'&E&_).
                       pose proof (sub_pom_T_internal e') as Ie'.
                       apply intersection_spec in Ie' as (Ie'&_).
                       apply V_spec in Ie' as (x&Ex).
                       rewrite E in Ex;discriminate.
                    ** apply EB;now left.
              -- destruct (@sub_pom_invert_list _ _ (get_par_right l) B') as (B''&<-).
                 ++ intros e Ie;apply get_par_right_spec.
                    cut ((inr e : ⌊ u∥v ⌋) ∈ map inr B');[|apply in_map_iff;exists e;tauto].
                    rewrite EB;intros I;apply in_map_iff in I as (x&<-&_).
                    pose proof (sub_pom_T_internal x) as Ix.
                    apply intersection_spec in Ix;tauto.
                 ++ erewrite map_map, <- map_ext,<-map_map in EB by apply hf.
                    destruct (𝒫_spec B'') as (B&IB&EB').
                    exists (map f B);split.
                    ** exists B;split;[reflexivity|split;[assumption|]].
                       exists (map (fun e => 𝒯e e) B'');split;[assumption|].
                       rewrite EB';reflexivity.
                    ** rewrite <- EB'.
                       intro e;transitivity (𝒯e e ∈ map (fun e => 𝒯e e) b).
                       --- rewrite in_map_iff.
                           split;[intro I;exists e;tauto|].
                           intros (x&E&Ix);apply is_injective in E as ->;assumption.
                       --- rewrite <- EB;symmetry.
                           rewrite (in_map_iff _ _ (𝒯e e)).
                           split;[intro I;exists e;tauto|].
                           intros (x&E&Ix);apply is_injective in E as ->;assumption.
      Qed.

      Lemma U_neg_V : ¬ U ≈ V.
      Proof.
        intro e;rewrite <- complement_spec.
        unfold U,V;repeat rewrite in_map_iff.
        split.
        - intros h;destruct e as [e|e].
          + exfalso;apply h;exists e;split;[reflexivity|apply domain_spec].
          + exists e;split;[reflexivity|apply domain_spec].
        - intros (e'&<-&_) (?&F&_);discriminate.
      Qed.

      Lemma U_full : u ≃ (u ∥ v) ⇂ U.
      Proof.
        rewrite <- inter_top.
        rewrite u_project.
        rewrite <- sub_pom_full at 1.
        apply sub_pom_proper.
        apply domain_equiv.
        intros x _.
        pose proof (@domain_spec (PomType (u∥v)) (inl x)) as I.
        apply get_par_left_spec,I.
      Qed.
      Lemma V_full : v ≃ (u ∥ v) ⇂ V.
      Proof.
        rewrite <- inter_top.
        rewrite v_project.
        rewrite <- sub_pom_full at 1.
        apply sub_pom_proper.
        apply domain_equiv.
        intros x _.
        pose proof (@domain_spec (PomType (u∥v)) (inr x)) as I.
        apply get_par_right_spec,I.
      Qed.
    End par_stuff.

    Section seq_stuff.
      Context {s t : Pomset X}.
      Definition S : list ⌊ s ⋅ t ⌋ := map inl ⟪PomType s⟫.
      Definition T : list ⌊ s ⋅ t ⌋ := map inr ⟪PomType t⟫.

      Remark S_spec e : e ∈ S <-> exists e' : ⌊s⌋ , e = inl e'.
      Proof.
        unfold S;rewrite in_map_iff;split.
        - intros (e'&<-&_);exists e';tauto.
        - intros (e'&->);exists e';split;[reflexivity|apply domain_spec].
      Qed.
      Remark T_spec e : e ∈ T <-> exists e' : ⌊t⌋ , e = inr e'.
      Proof.
        unfold T;rewrite in_map_iff;split.
        - intros (e'&<-&_);exists e';tauto.
        - intros (e'&->);exists e';split;[reflexivity|apply domain_spec].
      Qed.
      
      Lemma s_project l : (s⋅t) ⇂ (S ∩ l) ≃ s ⇂ (get_seq_left l).
      Proof.
        destruct (sub_pom_make_fun s (s⋅t) (get_seq_left l) (S∩l) inl)
          as (f&hf).
        - intros x Ix.
          apply in_map_iff in Ix as (y&<-&Iy).
          apply get_seq_left_spec in Iy.
          apply intersection_spec;split;[|assumption].
          apply in_map_iff;exists y;split;[reflexivity|apply domain_spec].
        - exists f;split.
          + split;split.
            * intros x y E.
              cut ((inl (𝒯e x) : ⌊ s ⋅ t ⌋)= inl (𝒯e y)).
              -- intro E';inversion E' as [E''].
                 revert E''; apply is_injective.
              -- repeat rewrite <- hf;rewrite E;reflexivity.
            * intros y.
              pose proof (sub_pom_T_internal y) as Iy.
              apply intersection_spec in Iy as (Ix&Iy).
              apply S_spec in Ix as (x&E).
              rewrite E in Iy.
              apply get_seq_left_spec,sub_pom_T_invert in Iy as (x'&<-).
              rewrite <- hf in E.
              apply is_injective in E as ->.
              exists x';reflexivity.
          + intro a.
            transitivity (ℓ (𝒯e (f a))).
            * reflexivity.
            * rewrite hf;reflexivity.
          + intros a a'.
            transitivity (inl (𝒯e a) ≤[s⋅t] inl (𝒯e a'));[reflexivity|].
            repeat rewrite <- hf;reflexivity.
          + split;intros b;setoid_rewrite in_map_iff;
              setoid_rewrite sub_pom_Boxes.
            * intros (B&<-&_&B'&IB'&E).
              destruct (𝒫_spec (map f B)) as (B''&IB''&EB'').
              exists B'';split;[split;[assumption|]|assumption].
              exists (map inl B');split.
              -- simpl;apply in_app_iff;left;apply in_map_iff;exists B';tauto.
              -- rewrite <- EB'',E.
                 repeat rewrite map_map.
                 symmetry;erewrite map_ext by apply hf;reflexivity.
            * intros (_&B&IB&EB).
              simpl in IB;apply in_app_iff in IB as [IB|IB];
                apply in_map_iff in IB as (B'&<-&IB').
              -- destruct (@sub_pom_invert_list _ _ (get_seq_left l) B') as (B''&<-).
                 ++ intros e Ie;apply get_seq_left_spec.
                    cut ((inl e : ⌊ s ⋅ t ⌋) ∈ map inl B');[|apply in_map_iff;exists e;tauto].
                    rewrite EB;intros I;apply in_map_iff in I as (x&<-&_).
                    pose proof (sub_pom_T_internal x) as Ix.
                    apply intersection_spec in Ix;tauto.
                 ++ erewrite map_map, <- map_ext,<-map_map in EB by apply hf.
                    destruct (𝒫_spec B'') as (B&IB&EB').
                    exists (map f B);split.
                    ** exists B;split;[reflexivity|split;[assumption|]].
                       exists (map (fun e => 𝒯e e) B'');split;[assumption|].
                       rewrite EB';reflexivity.
                    ** rewrite <- EB'.
                       intro e;transitivity (𝒯e e ∈ map (fun e => 𝒯e e) b).
                       --- rewrite in_map_iff.
                           split;[intro I;exists e;tauto|].
                           intros (x&E&Ix);apply is_injective in E as ->;assumption.
                       --- rewrite <- EB;symmetry.
                           rewrite (in_map_iff _ _ (𝒯e e)).
                           split;[intro I;exists e;tauto|].
                           intros (x&E&Ix);apply is_injective in E as ->;assumption.
              -- exfalso.
                 destruct B' as [|e B'].
                 ++ eapply Pomset_hnil,IB'.
                 ++ cut (inr e ∈ map (𝒯l {{S ∩ l}}) b).
                    ** intro I;apply in_map_iff in I as (e'&E&_).
                       pose proof (sub_pom_T_internal e') as Ie'.
                       apply intersection_spec in Ie' as (Ie'&_).
                       apply S_spec in Ie' as (x&Ex).
                       rewrite E in Ex;discriminate.
                    ** apply EB;now left.
      Qed.
      
      Lemma t_project l : (s⋅t) ⇂ (T ∩ l) ≃ t ⇂ (get_seq_right l).
      Proof.
        destruct (sub_pom_make_fun t (s⋅t) (get_seq_right l) (T∩l) inr)
          as (f&hf).
        - intros x Ix.
          apply in_map_iff in Ix as (y&<-&Iy).
          apply get_seq_right_spec in Iy.
          apply intersection_spec;split;[|assumption].
          apply in_map_iff;exists y;split;[reflexivity|apply domain_spec].
        - exists f;split.
          + split;split.
            * intros x y E.
              cut ((inr (𝒯e x) : ⌊ s ⋅ t ⌋)= inr (𝒯e y)).
              -- intro E';inversion E' as [E''].
                 revert E''; apply is_injective.
              -- repeat rewrite <- hf;rewrite E;reflexivity.
            * intros y.
              pose proof (sub_pom_T_internal y) as Iy.
              apply intersection_spec in Iy as (Ix&Iy).
              apply T_spec in Ix as (x&E).
              rewrite E in Iy.
              apply get_seq_right_spec,sub_pom_T_invert in Iy as (x'&<-).
              rewrite <- hf in E.
              apply is_injective in E as ->.
              exists x';reflexivity.
          + intro a.
            transitivity (ℓ (𝒯e (f a))).
            * reflexivity.
            * rewrite hf;reflexivity.
          + intros a a'.
            transitivity (inr (𝒯e a) ≤[s⋅t] inr (𝒯e a'));[reflexivity|].
            repeat rewrite <- hf;reflexivity.
          + split;intros b;setoid_rewrite in_map_iff;
              setoid_rewrite sub_pom_Boxes.
            * intros (B&<-&_&B'&IB'&E).
              destruct (𝒫_spec (map f B)) as (B''&IB''&EB'').
              exists B'';split;[split;[assumption|]|assumption].
              exists (map inr B');split.
              -- simpl;apply in_app_iff;right;apply in_map_iff;exists B';tauto.
              -- rewrite <- EB'',E.
                 repeat rewrite map_map.
                 symmetry;erewrite map_ext by apply hf;reflexivity.
            * intros (_&B&IB&EB).
              simpl in IB;apply in_app_iff in IB as [IB|IB];
                apply in_map_iff in IB as (B'&<-&IB').
              -- exfalso.
                 destruct B' as [|e B'].
                 ++ eapply Pomset_hnil,IB'.
                 ++ cut (inl e ∈ map (𝒯l {{T ∩ l}}) b).
                    ** intro I;apply in_map_iff in I as (e'&E&_).
                       pose proof (sub_pom_T_internal e') as Ie'.
                       apply intersection_spec in Ie' as (Ie'&_).
                       apply T_spec in Ie' as (x&Ex).
                       rewrite E in Ex;discriminate.
                    ** apply EB;now left.
              -- destruct (@sub_pom_invert_list _ _ (get_seq_right l) B') as (B''&<-).
                 ++ intros e Ie;apply get_seq_right_spec.
                    cut ((inr e : ⌊ s ⋅ t ⌋) ∈ map inr B');[|apply in_map_iff;exists e;tauto].
                    rewrite EB;intros I;apply in_map_iff in I as (x&<-&_).
                    pose proof (sub_pom_T_internal x) as Ix.
                    apply intersection_spec in Ix;tauto.
                 ++ erewrite map_map, <- map_ext,<-map_map in EB by apply hf.
                    destruct (𝒫_spec B'') as (B&IB&EB').
                    exists (map f B);split.
                    ** exists B;split;[reflexivity|split;[assumption|]].
                       exists (map (fun e => 𝒯e e) B'');split;[assumption|].
                       rewrite EB';reflexivity.
                    ** rewrite <- EB'.
                       intro e;transitivity (𝒯e e ∈ map (fun e => 𝒯e e) b).
                       --- rewrite in_map_iff.
                           split;[intro I;exists e;tauto|].
                           intros (x&E&Ix);apply is_injective in E as ->;assumption.
                       --- rewrite <- EB;symmetry.
                           rewrite (in_map_iff _ _ (𝒯e e)).
                           split;[intro I;exists e;tauto|].
                           intros (x&E&Ix);apply is_injective in E as ->;assumption.
      Qed.
      Lemma S_neg_T : ¬ S ≈ T.
      Proof.
        intro e;rewrite <- complement_spec.
        unfold S,T;repeat rewrite in_map_iff.
        split.
        - intros h;destruct e as [e|e].
          + exfalso;apply h;exists e;split;[reflexivity|apply domain_spec].
          + exists e;split;[reflexivity|apply domain_spec].
        - intros (e'&<-&_) (?&F&_);discriminate.
      Qed.    
      Lemma S_full : s ≃ (s ⋅ t) ⇂ S.
      Proof.
        rewrite <- inter_top.
        rewrite s_project.
        rewrite <- sub_pom_full at 1.
        apply sub_pom_proper.
        apply domain_equiv.
        intros x _.
        pose proof (@domain_spec (PomType (s⋅t)) (inl x)) as I.
        apply get_seq_left_spec,I.
      Qed.
      Lemma T_full : t ≃ (s ⋅ t) ⇂ T.
      Proof.
        rewrite <- inter_top.
        rewrite t_project.
        rewrite <- sub_pom_full at 1.
        apply sub_pom_proper.
        apply domain_equiv.
        intros x _.
        pose proof (@domain_spec (PomType (s⋅t)) (inr x)) as I.
        apply get_seq_right_spec,I.
      Qed.

    End seq_stuff.
    
    Lemma complement_F s t (f : ⟨s⟩ -> ⟨t⟩) :
      bijective f -> forall l , ¬ (map f l) ≈ map f ( ¬ l ) .
    Proof.
      intros B l e;repeat rewrite in_map_iff||setoid_rewrite <- complement_spec.
      split.
      - intros h.
        case_in (f ̃ e) l.
        + exfalso;apply h;exists (f ̃ e);split;[apply inverse_elim2|assumption].
        + exists (f̃ e);split;[apply inverse_elim2|assumption].
      - intros (e'&<-&Ie) (e''&E&F);apply is_injective in E as ->;apply Ie,F.
    Qed.

    Context {s t u v : Pomset X}.
   Proposition seq_par_split_hom :
      s ⋅ t ⊑o u ∥ v ->
      exists u1 u2 v1 v2,
        s ⊑o s ⇂ u1 ∥ s ⇂ v1
        /\ t ⊑o t ⇂ u2 ∥ t ⇂ v2
        /\ s ⇂ u1 ⋅ t ⇂ u2 ⊑o u
        /\ s ⇂ v1 ⋅ t ⇂ v2 ⊑o v.
    Proof.
      intros (f&hf).
      set (F := map f).
      set (U' := F U).
      set (V' := F V).
      set (u1 := (s ⋅ t) ⇂ (S ∩ U')).
      set (v1 := (s ⋅ t) ⇂ (S ∩ V')).
      set (u2 := (s ⋅ t) ⇂ (T ∩ U')).
      set (v2 := (s ⋅ t) ⇂ (T ∩ V')).
      exists (get_seq_left U'),(get_seq_right U'),(get_seq_left V'),(get_seq_right V');
        repeat split.
      - set (u' := get_seq_left U'). 
        set (v' := get_seq_left V').
        set (g := fun x : ⌊ s ⇂ u' ∥ s ⇂ v' ⌋ =>
                      match x with
                      | inl e => 𝒯e e
                      | inr e => 𝒯e e
                      end).
        cut (bijective g);[intro Bij;exists g;split;try assumption|].
        * intros [x|x];reflexivity.
        * intros [x|x] [y|y];simpl;try tauto.
        * split.
          -- intros b Ib.
            apply in_map_iff in Ib as (b'&<-&Ib').
            apply in_app_iff in Ib' as [Ib'|Ib'].
            ++ apply in_map_iff in Ib' as (b&<-&Ib).
               apply smaller_sets_singl in Ib.
               apply (@Embedding_box _ _ _ _ (sub_pom_Embedding s u')) in Ib.
               assert (I: map (𝒯l {{u'}}) b ∈ [map (𝒯l {{u'}}) b]) by now left.
               apply Ib in I as (b'&Ib'&Eb').
               exists b';split;[assumption|].
               rewrite map_map;simpl;apply Eb'.
            ++ apply in_map_iff in Ib' as (b&<-&Ib).
               apply smaller_sets_singl in Ib.
               apply (@Embedding_box _ _ _ _ (sub_pom_Embedding s v')) in Ib.
               assert (I: map (𝒯l {{v'}}) b ∈ [map (𝒯l {{v'}}) b]) by now left.
               apply Ib in I as (b'&Ib'&Eb').
               exists b';split;[assumption|].
               rewrite map_map;simpl;apply Eb'.
          -- intros b Ib.
            setoid_rewrite in_map_iff.
            simpl.
            setoid_rewrite in_app_iff.
            setoid_rewrite in_map_iff.
            setoid_rewrite sub_pom_box_spec.
            assert (Ib' : map inl b ∈ Boxes (s⋅t)) by
                (simpl;apply in_app_iff;left;apply in_map_iff;exists b;tauto).
            apply (@order_Boxes _ _ _ hf) in Ib' as (b'&Ib'&Eb').
            apply in_map_iff in Ib' as (b''&<-&Ib').
            simpl in Ib';apply in_app_iff in Ib' as [Ib'|Ib'].
            ++ apply in_map_iff in Ib' as (b'&<-&_).
               assert (hyp: b ⊆ u').
               ** cut (map inl b ⊆ U').
                 --- intros h x Ix.
                     apply get_seq_left_spec,h,in_map_iff;exists x;tauto.
                  --- rewrite Eb'.
                     intros x Ix;apply in_map_iff in Ix as (y&<-&Iy).
                     apply in_map_iff in Iy as (x&<-&Ix).
                     apply in_map_iff;exists (inl x);split;[reflexivity|].
                     apply U_spec;exists x;tauto.
               ** apply sub_pom_invert_list in hyp as (B&<-).
                  destruct (𝒫_spec B) as (B'&IB'&EB').
                  exists (map (𝒯l {{u'}}) B');split;[|rewrite EB';reflexivity].
                  destruct (@is_surjective _ _ (map g) _ (map (𝒯l {{u'}}) B'))
                    as (B''&EB'').
                  exists B'';split;[assumption|].
                  left.
                  exists B';split;[|split;[assumption|]].
                  --- apply (@is_injective _ _ (map g));[typeclasses eauto|].
                     rewrite EB'',map_map.
                     unfold g;reflexivity.
                  --- exists (map (𝒯l {{u'}}) B);split;[assumption|].
                     rewrite EB';reflexivity.
            ++ apply in_map_iff in Ib' as (b'&<-&_).
               assert (hyp: b ⊆ v').
               ** cut (map inl b ⊆ V').
                 --- intros h x Ix.
                    apply get_seq_left_spec,h,in_map_iff;exists x;tauto.
                  --- rewrite Eb'.
                     intros x Ix;apply in_map_iff in Ix as (y&<-&Iy).
                     apply in_map_iff in Iy as (x&<-&Ix).
                     apply in_map_iff;exists (inr x);split;[reflexivity|].
                     apply V_spec;exists x;tauto.
               ** apply sub_pom_invert_list in hyp as (B&<-).
                  destruct (𝒫_spec B) as (B'&IB'&EB').
                  exists (map (𝒯l {{v'}}) B');split;[|rewrite EB';reflexivity].
                  destruct (@is_surjective _ _ (map g) _ (map (𝒯l {{v'}}) B'))
                    as (B''&EB'').
                  exists B'';split;[assumption|].
                  right.
                  exists B';split;[|split;[assumption|]].
                 --- apply (@is_injective _ _ (map g));[typeclasses eauto|].
                     rewrite EB'',map_map.
                     unfold g;reflexivity.
                  --- exists (map (𝒯l {{v'}}) B);split;[assumption|].
                     rewrite EB';reflexivity.
        * unfold g in *;split;split.
          -- assert (h : forall (l : list ⌊s⌋)(x : ⌊s⇂l⌋),
                       { y : ⌊s⋅t⌋ | y = @inl ⌊s⌋ ⌊t⌋ (𝒯l {{l}} x)})
              by (intros l x;exists (inl (𝒯e x));reflexivity).
            intros [x|x] [y|y];intro E.
            ++ apply is_injective in E as ->;reflexivity.
            ++ exfalso.
               pose proof (h u' x) as (x'&Ex).
               pose proof (h v' y) as (y'&Ey).
               cut (x' ∈ F U /\ y' ∈ ¬ (F U)).
              ** rewrite <- complement_spec.
                  rewrite Ey,<-E,<-Ex;tauto.
               ** split.
                 --- rewrite Ex.
                     apply get_seq_left_spec.
                     apply sub_pom_T_internal.
                  --- rewrite Ey.
                     apply complement_F;[typeclasses eauto|].
                     rewrite U_neg_V.
                     apply get_seq_left_spec.
                     apply sub_pom_T_internal.
            ++ exfalso.
               pose proof (h v' x) as (x'&Ex).
               pose proof (h u' y) as (y'&Ey).
               cut (x' ∈ ¬ (F U) /\ y' ∈ F U).
              ** rewrite <- complement_spec.
                  rewrite Ey,<-E,<-Ex;tauto.
               ** split.
                  --- rewrite Ex.
                      
                     apply complement_F;[typeclasses eauto|].
                     rewrite U_neg_V.
                     apply get_seq_left_spec.
                     apply sub_pom_T_internal.
                  --- rewrite Ey.
                     apply get_seq_left_spec.
                     apply sub_pom_T_internal.
            ++ apply is_injective in E as ->;reflexivity.   
          -- intros y.
            case_in y u'.
            ++ apply sub_pom_T_invert in I as (y'&<-).
               exists (inl y');reflexivity.
            ++ cut (y ∈ v').
               ** clear I;intro I.
                  apply sub_pom_T_invert in I as (y'&<-).
                  exists (inr y');reflexivity.
               ** unfold u',U',v',V' in *.
                  rewrite get_seq_left_spec in *.
                  rewrite <- U_neg_V.
                  unfold F;rewrite <- (complement_F  _ _ f);[|typeclasses eauto].
                  replace (map f) with F by reflexivity.
                  revert I;generalize (F U);generalize (inl y : ⌊s⋅t⌋);clear.
                  intros x l.
                  rewrite (complement_spec x l).
                  tauto.
      - set (u' := get_seq_right U'). 
        set (v' := get_seq_right V').
        set (g := fun x : ⌊ t ⇂ u' ∥ t ⇂ v' ⌋ =>
                    match x with
                    | inl e => 𝒯e e
                    | inr e => 𝒯e e
                    end).
        cut (bijective g);[intro Bij;exists g;split;try assumption|].
        + intros [x|x];reflexivity.
        + intros [x|x] [y|y];simpl;try tauto.
        + split.
          * intros b Ib.
            apply in_map_iff in Ib as (b'&<-&Ib').
            apply in_app_iff in Ib' as [Ib'|Ib'].
            -- apply in_map_iff in Ib' as (b&<-&Ib).
               apply smaller_sets_singl in Ib.
               apply (@Embedding_box _ _ _ _ (sub_pom_Embedding t u')) in Ib.
               assert (I: map (𝒯l {{u'}}) b ∈ [map (𝒯l {{u'}}) b]) by now left.
               apply Ib in I as (b'&Ib'&Eb').
               exists b';split;[assumption|].
               rewrite map_map;simpl;apply Eb'.
            -- apply in_map_iff in Ib' as (b&<-&Ib).
               apply smaller_sets_singl in Ib.
               apply (@Embedding_box _ _ _ _ (sub_pom_Embedding t v')) in Ib.
               assert (I: map (𝒯l {{v'}}) b ∈ [map (𝒯l {{v'}}) b]) by now left.
               apply Ib in I as (b'&Ib'&Eb').
               exists b';split;[assumption|].
               rewrite map_map;simpl;apply Eb'.
          * intros b Ib.
            setoid_rewrite in_map_iff.
            simpl.
            setoid_rewrite in_app_iff.
            setoid_rewrite in_map_iff.
            setoid_rewrite sub_pom_box_spec.
            assert (Ib' : map inr b ∈ Boxes (s⋅t)) by
                (simpl;apply in_app_iff;right;apply in_map_iff;exists b;tauto).
            apply (@order_Boxes _ _ _ hf) in Ib' as (b'&Ib'&Eb').
            apply in_map_iff in Ib' as (b''&<-&Ib').
            simpl in Ib';apply in_app_iff in Ib' as [Ib'|Ib'].
            -- apply in_map_iff in Ib' as (b'&<-&_).
               assert (hyp: b ⊆ u').
               ** cut (map inr b ⊆ U').
                  --- intros h x Ix.
                     apply get_seq_right_spec,h,in_map_iff;exists x;tauto.
                  --- rewrite Eb'.
                     intros x Ix;apply in_map_iff in Ix as (y&<-&Iy).
                     apply in_map_iff in Iy as (x&<-&Ix).
                     apply in_map_iff;exists (inl x);split;[reflexivity|].
                     apply U_spec;exists x;tauto.
               ** apply sub_pom_invert_list in hyp as (B&<-).
                  destruct (𝒫_spec B) as (B'&IB'&EB').
                  exists (map (𝒯l {{u'}}) B');split;[|rewrite EB';reflexivity].
                  destruct (@is_surjective _ _ (map g) _ (map (𝒯l {{u'}}) B'))
                    as (B''&EB'').
                  exists B'';split;[assumption|].
                  left.
                  exists B';split;[|split;[assumption|]].
                  --- apply (@is_injective _ _ (map g));[typeclasses eauto|].
                     rewrite EB'',map_map.
                     unfold g;reflexivity.
                  --- exists (map (𝒯l {{u'}}) B);split;[assumption|].
                     rewrite EB';reflexivity.
            -- apply in_map_iff in Ib' as (b'&<-&_).
               assert (hyp: b ⊆ v').
               ** cut (map inr b ⊆ V').
                  --- intros h x Ix.
                     apply get_seq_right_spec,h,in_map_iff;exists x;tauto.
                  --- rewrite Eb'.
                     intros x Ix;apply in_map_iff in Ix as (y&<-&Iy).
                     apply in_map_iff in Iy as (x&<-&Ix).
                     apply in_map_iff;exists (inr x);split;[reflexivity|].
                     apply V_spec;exists x;tauto.
               ** apply sub_pom_invert_list in hyp as (B&<-).
                  destruct (𝒫_spec B) as (B'&IB'&EB').
                  exists (map (𝒯l {{v'}}) B');split;[|rewrite EB';reflexivity].
                  destruct (@is_surjective _ _ (map g) _ (map (𝒯l {{v'}}) B'))
                    as (B''&EB'').
                  exists B'';split;[assumption|].
                  right.
                  exists B';split;[|split;[assumption|]].
                  --- apply (@is_injective _ _ (map g));[typeclasses eauto|].
                     rewrite EB'',map_map.
                     unfold g;reflexivity.
                  --- exists (map (𝒯l {{v'}}) B);split;[assumption|].
                     rewrite EB';reflexivity.
        + unfold g in *;split;split.
          * assert (h : forall (l : list ⌊t⌋)(x : ⌊t⇂l⌋),
                       { y : ⌊s⋅t⌋ | y = @inr ⌊s⌋ ⌊t⌋ (𝒯l {{l}} x)})
              by (intros l x;exists (inr (𝒯e x));reflexivity).
            intros [x|x] [y|y];intro E.
            -- apply is_injective in E as ->;reflexivity.
            -- exfalso.
               pose proof (h u' x) as (x'&Ex).
               pose proof (h v' y) as (y'&Ey).
               cut (x' ∈ F U /\ y' ∈ ¬ (F U)).
               ** rewrite <- complement_spec.
                  rewrite Ey,<-E,<-Ex;tauto.
               ** split.
                  --- rewrite Ex.
                     apply get_seq_right_spec.
                     apply sub_pom_T_internal.
                  --- rewrite Ey.
                     apply complement_F;[typeclasses eauto|].
                     rewrite U_neg_V.
                     apply get_seq_right_spec.
                     apply sub_pom_T_internal.
            -- exfalso.
               pose proof (h v' x) as (x'&Ex).
               pose proof (h u' y) as (y'&Ey).
               cut (x' ∈ ¬ (F U) /\ y' ∈ F U).
               ** rewrite <- complement_spec.
                  rewrite Ey,<-E,<-Ex;tauto.
               ** split.
                  --- rewrite Ex.
                     apply complement_F;[typeclasses eauto|].
                     rewrite U_neg_V.
                     apply get_seq_right_spec.
                     apply sub_pom_T_internal.
                  --- rewrite Ey.
                     apply get_seq_right_spec.
                     apply sub_pom_T_internal.
            -- apply is_injective in E as ->;reflexivity.   
          * intros y.
            case_in y u'.
            -- apply sub_pom_T_invert in I as (y'&<-).
               exists (inl y');reflexivity.
            -- cut (y ∈ v').
               ** clear I;intro I.
                  apply sub_pom_T_invert in I as (y'&<-).
                  exists (inr y');reflexivity.
               ** unfold u',U',v',V' in *.
                  rewrite get_seq_right_spec in *.
                  rewrite <- U_neg_V.
                  unfold F;rewrite <- complement_F by (typeclasses eauto).
                  replace (map f) with F by reflexivity.
                  revert I;generalize (F U);generalize (inr y : ⌊s⋅t⌋);clear.
                  intros x l.
                  rewrite (complement_spec x l).
                  tauto.
      - transitivity ((u∥v)⇂U);[|apply order_subsumption_equiv;symmetry;apply U_full].
        transitivity ((s⋅t)⇂U');[|apply lift_order,hf].
        apply order_subsumption_equiv.
        apply sub_pom_seq_dec.
      - transitivity ((u∥v)⇂V);[|apply order_subsumption_equiv;symmetry;apply V_full].
        transitivity ((s⋅t)⇂V');[|apply lift_order,hf].
        apply order_subsumption_equiv.
        apply sub_pom_seq_dec.
    Qed.
  End seq_par_split_hom.

  Fixpoint bsp_sizeb (t : bsp_terms X) :=
    match t with
    | bsp_var _ => 1
    | bsp_unit => 0
    | bsp_box t => 1 + bsp_sizeb t
    | bsp_seq t1 t2 | bsp_par t1 t2 => bsp_sizeb t1 + bsp_sizeb t2
    end.

  Lemma bsp_sizeb_size t : ⎢t⎥ <= bsp_sizeb t.
  Proof. induction t;rsimpl;lia. Qed.

  Definition pom_sizeb (P : Pomset X) := ⎢P⎥ + ⎢undupEq (Boxes P)⎥.

  Lemma smaller_sets_undupEq_size t :
    forall l m : list (list ⟨ t ⟩), l ≲ m -> ⎢ undupEq l ⎥ <= ⎢ undupEq m ⎥.
  Proof.
    induction l;intros m;[rsimpl;lia|].
    intros Ia;simpl.
    case_eq (forallb (fun b => negb (equivalentb a b)) l).
    - rsimpl.
      intros h.
      destruct (@dec_prop_powerset_bnd t (fun x => ~ (a ≈ x)) (undupEq m))
        as (m'&Em');
        [typeclasses eauto|].
      etransitivity;[apply le_n_S,(IHl m')|].
      + intros x Ix.
        assert (x ∈ (a::l)) as I by now right.
        apply Ia in I as (b'&I&E).
        apply undupEq_eq in I as (b&I&E').
        rewrite E' in E;clear b' E'.
        exists b;split;[|assumption].
        apply Em';split;[assumption|].
        rewrite forallb_forall in h.
        setoid_rewrite negb_true_iff in h.
        setoid_rewrite <- not_true_iff_false in h.
        setoid_rewrite equivalentb_spec in h.
        rewrite <- E.
        apply h,Ix.
      + assert (a ∈ (a::l)) as I by now left.
        apply Ia in I as (b'&I&E).
        apply undupEq_eq in I as (b&I&E').
        rewrite E' in E;clear b' E'.
        transitivity ⎢b::undupEq m'⎥;[reflexivity|].
        pose proof (undupEq_spec m') as (_&hm'&_).
        apply NoDup_length.
        -- intros x [<-|Ix].
           ++ assumption.
           ++ apply hm',Em' in Ix;tauto.
        -- apply NoDupEq_NoDup.
           simpl;split.
           ++ intros x Ix.
              apply hm',Em' in Ix.
              rewrite E in Ix;tauto.
           ++ apply undupEq_NoDupEq.
    - intro I.
      apply IHl.
      intros x Ix;apply Ia;now right.
  Qed.

  Lemma equiv_sets_undupEq_size t :
    forall l m : list (list ⟨ t ⟩), l ≃ m -> ⎢ undupEq l ⎥ = ⎢ undupEq m ⎥.
  Proof.
    intros l m (h1&h2);apply antisymmetry;apply smaller_sets_undupEq_size;assumption.
  Qed.
  
  Lemma pom_sizeb_order_subsumption P Q : P ⊑o Q -> pom_sizeb P = pom_sizeb Q.
  Proof.
    intros h;unfold pom_sizeb.
    pose proof h as h';apply order_subsumption_smaller,sizePomset_subsumption in h' as <- .
    f_equal.
    destruct h as (f&h).
    pose proof order_Boxes as E.
    transitivity ⎢map (map f) (undupEq (Boxes Q))⎥;[|rsimpl;reflexivity].
    rewrite <- undupEq_map by (typeclasses eauto).
    symmetry;apply equiv_sets_undupEq_size,E.
  Qed.
  
  Lemma undupEq_app_proj s t :
    forall (l : list (list ⟨ s ⟩)) (m : list (list ⟨ t ⟩)),
      ~ [] ∈ m -> 
      undupEq (map (map (fun e : ⟨s⟩=> inl e : ⟨s⊎t⟩)) l)
              ++ undupEq (map (map (fun e : ⟨t⟩=> inr e : ⟨s⊎t⟩)) m) =
      undupEq (map (map (fun e : ⟨s⟩=> inl e : ⟨s⊎t⟩)) l
                   ++ (map (map (fun e : ⟨t⟩=> inr e : ⟨s⊎t⟩)) m)).
  Proof.
    intros l m hm.
    induction l;[reflexivity|].
    simpl.
    case_eq (forallb (fun b : list (⟨ s ⟩ + ⟨ t ⟩)=>
                        negb (equivalentb  (map (fun e : ⟨ s ⟩ => inl e : ⟨s⊎t⟩) a) b))
                     (map (map (fun e : ⟨ s ⟩ => inl e : ⟨s⊎t⟩)) l)).
    - intro E.
      replace (forallb _ _) with true.
      replace (forallb _ _) with true.
      + simpl;f_equal.
        apply IHl. 
      + rewrite forallb_forall in E.
        symmetry;apply forallb_forall.
        intros x Ix.
        apply in_app_iff in Ix as [Ix|Ix];apply in_map_iff in Ix as (y&<-&Iy).
        * apply E,in_map_iff;exists y;tauto.
        * unfold equivalentb.
          rewrite negb_true_iff,andb_false_iff.
          right;apply forallb_false_exists.
          destruct y as [|e y].
          -- exfalso;apply hm,Iy.
          -- exists (inr e);split.
             ++ now left.
             ++ apply not_true_iff_false;intro F.
                apply inb_spec,in_map_iff in F as (?&F&_);discriminate.
    - intros E.
      replace (forallb _ _) with false.
      replace (forallb _ _) with false.
      + apply IHl.
      + symmetry.
        apply forallb_false_exists in E as (x&Ix&Ex).
        apply forallb_false_exists;exists x;split;[|assumption].
        apply in_app_iff;tauto.
  Qed.
  
  Lemma clean_terms_sizeb t :
    is_bsp_clean t -> bsp_sizeb t = pom_sizeb ⟦t⟧.
  Proof.
    induction t.
    - intros (C1&C2);rsimpl.
      rewrite IHt1,IHt2 by assumption.
      unfold pom_sizeb;rsimpl.
      rewrite sizePomset_seq.
      replace (undupEq (map (map inl) (Boxes ⟦ t1 ⟧) ++ map (map inr) (Boxes ⟦ t2 ⟧)))
        with (undupEq (map (map inl) (Boxes ⟦ t1 ⟧)) ++
                      undupEq (map (map inr) (Boxes ⟦ t2 ⟧))).
      + repeat rewrite undupEq_map by typeclasses eauto.
        rewrite SizeApp;rsimpl;lia.
      + pose proof (@Pomset_hnil X ⟦t2⟧) as hm;revert hm.
        generalize (Boxes ⟦ t2 ⟧);generalize (Boxes ⟦ t1 ⟧).
        generalize (PomType ⟦t2⟧);generalize (PomType ⟦t1⟧).
        clear;intros s t l m hm.
        induction l.
        * simpl;clear;induction m;simpl;auto.
          case_eq (forallb (fun b : list (⟨ s ⟩ + ⟨ t ⟩) => negb (equivalentb (map inr a) b))
                           (map (map inr) m)).
          -- intro E;replace (forallb _ _) with true.
             ++ rewrite IHm;reflexivity.
             ++ symmetry.
                rewrite forallb_forall in E.
                setoid_rewrite negb_true_iff in E.
                setoid_rewrite <- not_true_iff_false in E.
                setoid_rewrite equivalentb_spec in E.
                apply forallb_forall;intros x Ix.
                rewrite negb_true_iff,<- not_true_iff_false,equivalentb_spec.
                apply E,Ix.
          -- intro E;replace (forallb _ _) with false;[assumption|].
             symmetry.
             apply forallb_false_exists in E as (b&Ib&Eb).
             rewrite negb_false_iff,equivalentb_spec in Eb.
             apply forallb_false_exists;exists b;split;[assumption|].
             rewrite negb_false_iff,equivalentb_spec;assumption.
        * simpl.
          case_eq (forallb (fun b : list (⟨ s ⟩ + ⟨ t ⟩) => negb (equivalentb (map inl a) b))
                           (map (map inl) l)).
          -- intro E.
             replace (forallb _ _) with true.
             ++ simpl;f_equal.
                apply IHl. 
             ++ rewrite forallb_forall in E.
                symmetry;apply forallb_forall.
                intros x Ix.
                apply in_app_iff in Ix as [Ix|Ix];apply in_map_iff in Ix as (y&<-&Iy).
                ** setoid_rewrite negb_true_iff in E.
                   setoid_rewrite <- not_true_iff_false in E.
                   setoid_rewrite equivalentb_spec in E.
                   rewrite negb_true_iff,<- not_true_iff_false,equivalentb_spec.
                   apply E,in_map_iff;exists y;tauto.
                ** unfold equivalentb.
                   rewrite negb_true_iff,andb_false_iff.
                   right;apply forallb_false_exists.
                   destruct y as [|e y].
                   --- exfalso;apply hm,Iy.
                   --- exists (inr e);split.
                       +++ now left.
                       +++ apply not_true_iff_false;intro F.
                           apply inb_spec,in_map_iff in F as (?&F&_);discriminate.
          -- intros E.
             replace (forallb _ _) with false.
             ++ apply IHl.
             ++ symmetry.
                apply forallb_false_exists in E as (b&Ib&Eb).
                rewrite negb_false_iff,equivalentb_spec in Eb.
                apply forallb_false_exists;exists b;split.
                ** apply in_app_iff;tauto.
                ** rewrite negb_false_iff,equivalentb_spec;assumption.
    - intros (C1&C2);rsimpl.
      rewrite IHt1,IHt2 by assumption.
      unfold pom_sizeb;rsimpl.
      rewrite sizePomset_par.
      replace (undupEq (map (map inl) (Boxes ⟦ t1 ⟧) ++ map (map inr) (Boxes ⟦ t2 ⟧)))
        with (undupEq (map (map inl) (Boxes ⟦ t1 ⟧)) ++
                      undupEq (map (map inr) (Boxes ⟦ t2 ⟧))).
      + repeat rewrite undupEq_map by typeclasses eauto.
        rewrite SizeApp;rsimpl;lia.
      + pose proof (@Pomset_hnil X ⟦t2⟧) as hm;revert hm.
        generalize (Boxes ⟦ t2 ⟧);generalize (Boxes ⟦ t1 ⟧).
        generalize (PomType ⟦t2⟧);generalize (PomType ⟦t1⟧).
        clear;intros s t l m hm.
        induction l.
        * simpl;clear;induction m;simpl;auto.
          case_eq (forallb (fun b : list (⟨ s ⟩ + ⟨ t ⟩) => negb (equivalentb (map inr a) b))
                           (map (map inr) m)).
          -- intro E;replace (forallb _ _) with true.
             ++ rewrite IHm;reflexivity.
             ++ symmetry.
                rewrite forallb_forall in E.
                setoid_rewrite negb_true_iff in E.
                setoid_rewrite <- not_true_iff_false in E.
                setoid_rewrite equivalentb_spec in E.
                apply forallb_forall;intros x Ix.
                rewrite negb_true_iff,<- not_true_iff_false,equivalentb_spec.
                apply E,Ix.
          -- intro E;replace (forallb _ _) with false;[assumption|].
             symmetry.
             apply forallb_false_exists in E as (b&Ib&Eb).
             rewrite negb_false_iff,equivalentb_spec in Eb.
             apply forallb_false_exists;exists b;split;[assumption|].
             rewrite negb_false_iff,equivalentb_spec;assumption.
        * simpl.
          case_eq (forallb (fun b : list (⟨ s ⟩ + ⟨ t ⟩) => negb (equivalentb (map inl a) b))
                           (map (map inl) l)).
          -- intro E.
             replace (forallb _ _) with true.
             ++ simpl;f_equal.
                apply IHl. 
             ++ rewrite forallb_forall in E.
                symmetry;apply forallb_forall.
                intros x Ix.
                apply in_app_iff in Ix as [Ix|Ix];apply in_map_iff in Ix as (y&<-&Iy).
                ** setoid_rewrite negb_true_iff in E.
                   setoid_rewrite <- not_true_iff_false in E.
                   setoid_rewrite equivalentb_spec in E.
                   rewrite negb_true_iff,<- not_true_iff_false,equivalentb_spec.
                   apply E,in_map_iff;exists y;tauto.
                ** unfold equivalentb.
                   rewrite negb_true_iff,andb_false_iff.
                   right;apply forallb_false_exists.
                   destruct y as [|e y].
                   --- exfalso;apply hm,Iy.
                   --- exists (inr e);split.
                       +++ now left.
                       +++ apply not_true_iff_false;intro F.
                           apply inb_spec,in_map_iff in F as (?&F&_);discriminate.
          -- intros E.
             replace (forallb _ _) with false.
             ++ apply IHl.
             ++ symmetry.
                apply forallb_false_exists in E as (b&Ib&Eb).
                rewrite negb_false_iff,equivalentb_spec in Eb.
                apply forallb_false_exists;exists b;split.
                ** apply in_app_iff;tauto.
                ** rewrite negb_false_iff,equivalentb_spec;assumption.
    - unfold pom_sizeb;simpl;rsimpl;reflexivity.
    - intros C.
      assert (is_bsp_clean t) as Ct by (destruct t;(apply C)||(exfalso;apply C)).
      apply bsp_get_box_Boxes in Ct.
      simpl.
      rewrite IHt by (destruct t;(apply C)||(exfalso;apply C)).
      unfold pom_sizeb.
      replace (bsp_box t) with (box t) by reflexivity.
      rewrite Ct.
      rsimpl.
      replace ⟪ PomType (sem_bsp t) ⟫ with ⟨|t|⟩ by reflexivity.
      rewrite sizePomset_box.
      unfold bsp_get_box.
      erewrite map_ext,map_id by apply map_id.
      case_eq (forallb (fun b : list ⌊ sem_bsp t ⌋ => negb (equivalentb ⟨| t |⟩ b)) (Boxes ⟦ t ⟧)).
      + intro E.
        replace (forallb _ _) with true.
        rsimpl.
        rewrite Nat.add_succ_r;reflexivity.
      + intro F;exfalso.
        apply forallb_false_exists in F as (b&Ib&Eb).
        apply negb_false_iff,equivalentb_spec in Eb.
        symmetry in Eb;revert Eb;apply is_bsp_clean_box_domain;assumption.
    - reflexivity.
  Qed.

  Remark bsp_sizeb_clean s : is_bsp_clean s -> 0 < bsp_sizeb s.
  Proof.
    intro C; apply is_bsp_clean_bsp_size in C;pose proof (bsp_sizeb_size s) as L;lia.
  Qed.
        
  Proposition completeness_order_hom : forall s t : bsp_terms X, ⟦ s ⟧ ⊑o ⟦ t ⟧ -> s ⊑ t.
  Proof.
    intros s t hyp.
    rewrite (bsp_clean_eq t).
    cut (⟦s⟧ ⊑o ⟦bsp_clean t⟧);
      [|
       etransitivity;[|apply order_subsumption_equiv;rewrite <- bsp_clean_eq;reflexivity];
       assumption
      ].
    clear hyp.
    destruct (bsp_clean_is_bsp_clean t) as [->|Ct];
      [intro E;apply bsp_subs_eq,unit_split_hom;tauto|].
    generalize dependent (bsp_clean t);clear t;intro t;revert s.
    set (N := bsp_sizeb t).
    assert (h__N: bsp_sizeb t <= N) by reflexivity.
    generalize dependent N;intros N hN s;revert t s hN;induction N.
    - intros t s L C;exfalso.
      apply bsp_sizeb_clean in C;lia.
    - intros [t1 t2|t1 t2|a|t|] s Len C hyp;rsimpl in *.
      + apply seq_right_split_hom in hyp as (l&E&h1&h2).
        destruct C as (C1&C2).
        pose proof (bsp_sizeb_clean _ C1) as L1.
        pose proof (bsp_sizeb_clean _ C2) as L2.
        apply IHN in h1;[|lia|tauto].
        apply IHN in h2;[|lia|tauto].
        rewrite E,h1,h2;reflexivity.
      + destruct C as (C1&C2).
        pose proof (bsp_sizeb_clean _ C1) as L1.
        pose proof (bsp_sizeb_clean _ C2) as L2.
        pose proof (bsp_clean_eq s) as Es.
        rewrite Es.
        symmetry in Es.
        apply soundness_bsp_terms,order_subsumption_equiv in Es.
        rewrite <- Es in hyp.
        clear Es;revert hyp.
        destruct (bsp_clean_is_bsp_clean s) as [->|Cs];intro hyp.
        * apply subs_eq;symmetry.
          apply unit_split_hom;tauto.
        * generalize dependent (bsp_clean s);clear s;intros s Cs hyp.
          assert (Sz : bsp_sizeb s = bsp_sizeb (t1∥t2))
            by (rewrite clean_terms_sizeb by assumption;
                rewrite clean_terms_sizeb by (simpl;tauto);
                apply pom_sizeb_order_subsumption,hyp).
          destruct s.
          -- rsimpl in *.
             apply seq_par_split_hom in hyp as (u1&u2&v1&v2&I1&I2&I3&I4).
             pose proof (sub_term_sub_pom s1 u1) as Eu1.
             pose proof (sub_term_sub_pom s2 u2) as Eu2.
             pose proof (sub_term_sub_pom s1 v1) as Ev1.
             pose proof (sub_term_sub_pom s2 v2) as Ev2.
             rewrite <- (order_subsumption_equiv _ _ Eu1) in I3.
             rewrite <- (order_subsumption_equiv _ _ Eu2) in I3.
             rewrite <- (order_subsumption_equiv _ _ Ev1) in I4.
             rewrite <- (order_subsumption_equiv _ _ Ev2) in I4.
             symmetry in Eu1,Eu2,Ev1,Ev2.
             rewrite (order_subsumption_equiv _ _ Eu1) in I1.
             rewrite (order_subsumption_equiv _ _ Eu2) in I2.
             rewrite (order_subsumption_equiv _ _ Ev1) in I1.
             rewrite (order_subsumption_equiv _ _ Ev2) in I2.
             revert I1 I2 I3 I4;clear Eu1 Eu2 Ev1 Ev2.
             generalize (s2⨡v2);generalize (s1⨡v1);generalize (s2⨡u2);generalize (s1 ⨡ u1);
               clear u1 u2 v1 v2;intros u1 u2 v1 v2.
             pose proof  (soundness_bsp_terms (bsp_clean_eq u1)) as E.
             rewrite (order_subsumption_equiv _ _ E) at 1;symmetry in E;
               rewrite <- (order_subsumption_equiv _ _ E) at 1;clear E.
             pose proof  (soundness_bsp_terms (bsp_clean_eq v1)) as E.
             rewrite (order_subsumption_equiv _ _ E) at 1;symmetry in E;
               rewrite <- (order_subsumption_equiv _ _ E) at 1;clear E.
             pose proof  (soundness_bsp_terms (bsp_clean_eq u2)) as E.
             rewrite (order_subsumption_equiv _ _ E) at 1;symmetry in E;
               rewrite <- (order_subsumption_equiv _ _ E) at 1;clear E.
             pose proof  (soundness_bsp_terms (bsp_clean_eq v2)) as E.
             rewrite (order_subsumption_equiv _ _ E) at 1;symmetry in E;
               rewrite <- (order_subsumption_equiv _ _ E) at 1;clear E.
             intros I1 I2 I3 I4.
             assert (Es1 : ⟦ s1 ⟧ ⊑o ⟦ bsp_clean u1 ∥ bsp_clean v1 ⟧) by apply I1;clear I1.
             assert (Es2 : ⟦ s2 ⟧ ⊑o ⟦ bsp_clean u2 ∥ bsp_clean v2 ⟧) by apply I2;clear I2.
             assert (Et1 : ⟦ bsp_clean u1 ⋅ bsp_clean u2 ⟧ ⊑o ⟦ t1 ⟧) by apply I3;
               clear I3.
             assert (Et2 : ⟦ bsp_clean v1 ⋅ bsp_clean v2 ⟧ ⊑o ⟦ t2 ⟧) by apply I4;
               clear I4.
             apply IHN in Et1 as <- ;[|lia|tauto].
             apply IHN in Et2 as <- ;[|lia|tauto].
             rewrite <- subs_exchange.
             destruct Cs as (Cs1&Cs2).
             pose proof (bsp_sizeb_clean _ Cs1) as Ls1.
             pose proof (bsp_sizeb_clean _ Cs2) as Ls2.
             apply subs_seq.
             ++ revert Es1 Es2;destruct (bsp_clean_is_bsp_clean u1) as [->|Cu1];
                  destruct (bsp_clean_is_bsp_clean v1) as [->|Cv1];intros Es1 Es2.
                ** rewrite left_unit.
                   apply subs_eq,bsp_size_unit.
                   apply order_subsumption_smaller in Es1.
                   apply sizePomset_subsumption in Es1.
                   rewrite <- interpret_bsp_size in Es1.
                   apply Es1.
                ** rewrite left_unit.
                   cut (⟦ s1 ⟧ ⊑o ⟦ bsp_clean v1 ⟧).
                   --- intro O.
                       apply IHN;auto.
                       apply pom_sizeb_order_subsumption in O.
                       rewrite <- clean_terms_sizeb in O by tauto.
                       rewrite <- clean_terms_sizeb in O by tauto.
                       lia.
                   --- rewrite Es1.
                       apply order_subsumption_equiv,soundness_bsp_terms,left_unit.
                ** rewrite right_unit.
                   cut (⟦ s1 ⟧ ⊑o ⟦ bsp_clean u1 ⟧).
                   --- intro O.
                       apply IHN;auto.
                       apply pom_sizeb_order_subsumption in O.
                       rewrite <- clean_terms_sizeb in O by tauto.
                       rewrite <- clean_terms_sizeb in O by tauto.
                       lia.
                   --- rewrite Es1.
                       apply order_subsumption_equiv,soundness_bsp_terms,right_unit.
                ** apply IHN;simpl;auto.
                   apply pom_sizeb_order_subsumption in Es1.
                   repeat rewrite <- clean_terms_sizeb in Es1 by (simpl;tauto).
                   simpl in Es1.
                   rewrite <- Es1.
                   lia.
             ++ revert Es1 Es2;destruct (bsp_clean_is_bsp_clean u2) as [->|Cu2];
                  destruct (bsp_clean_is_bsp_clean v2) as [->|Cv2];intros Es1 Es2.
                ** rewrite left_unit.
                   apply subs_eq,bsp_size_unit.
                   apply order_subsumption_smaller in Es2.
                   apply sizePomset_subsumption in Es2.
                   rewrite <- interpret_bsp_size in Es2.
                   apply Es2.
                ** rewrite left_unit.
                   cut (⟦ s2 ⟧ ⊑o ⟦ bsp_clean v2 ⟧).
                   --- intro O.
                       apply IHN;auto.
                       apply pom_sizeb_order_subsumption in O.
                       rewrite <- clean_terms_sizeb in O by tauto.
                       rewrite <- clean_terms_sizeb in O by tauto.
                       lia.
                   --- rewrite Es2.
                       apply order_subsumption_equiv,soundness_bsp_terms,left_unit.
                ** rewrite right_unit.
                   cut (⟦ s2 ⟧ ⊑o ⟦ bsp_clean u2 ⟧).
                   --- intro O.
                       apply IHN;auto.
                       apply pom_sizeb_order_subsumption in O.
                       rewrite <- clean_terms_sizeb in O by tauto.
                       rewrite <- clean_terms_sizeb in O by tauto.
                       lia.
                   --- rewrite Es2.
                       apply order_subsumption_equiv,soundness_bsp_terms,right_unit.
                ** apply IHN;simpl;auto.
                   apply pom_sizeb_order_subsumption in Es2.
                   repeat rewrite <- clean_terms_sizeb in Es2 by (simpl;tauto).
                   simpl in Es2.
                   rewrite <- Es2.
                   lia.
          -- assert (O: ⟦ s1 ∥ s2 ⟧ ⊑o ⟦ t1 ∥ t2 ⟧) by (apply hyp);clear hyp.
             apply par_left_split_hom in O as (l&Et&I1&I2).
             generalize dependent ((t1 ∥ t2) ⨡ ¬ (t:=PomType ⟦ t1 ∥ t2 ⟧) l).
             generalize dependent ((t1 ∥ t2) ⨡ l).
             intros u1 I1 u2 Et I2.
             replace (bsp_par s1 s2) with (s1 ∥ s2) by reflexivity.
             simpl in Sz.
             destruct Cs as (Cs1&Cs2).
             pose proof (bsp_sizeb_clean _ Cs1) as S1.
             pose proof (bsp_sizeb_clean _ Cs2) as S2.
             rewrite Et.
             apply subs_par.
             ++ rewrite (bsp_clean_eq u1).
                rewrite (order_subsumption_equiv _ _
                                                 (soundness_bsp_terms (bsp_clean_eq u1)))
                  in I1;revert I1.
                destruct (bsp_clean_is_bsp_clean u1) as [->|C].
                ** intro F.
                   apply pom_sizeb_order_subsumption in F.
                   rewrite <- clean_terms_sizeb in F by assumption.
                   exfalso.
                   revert S1.
                   rewrite F;simpl.
                   unfold pom_sizeb;simpl.
                   rsimpl;lia.
                ** intro I1;apply IHN;auto.
                   apply pom_sizeb_order_subsumption in I1.
                   repeat rewrite <- clean_terms_sizeb in I1 by assumption.
                   lia.
             ++ rewrite (bsp_clean_eq u2).
                rewrite (order_subsumption_equiv _ _
                                                 (soundness_bsp_terms (bsp_clean_eq u2)))
                  in I2;revert I2.
                destruct (bsp_clean_is_bsp_clean u2) as [->|C].
                ** intro F.
                   apply pom_sizeb_order_subsumption in F.
                   rewrite <- clean_terms_sizeb in F by assumption.
                   exfalso.
                   revert S2.
                   rewrite F;simpl.
                   unfold pom_sizeb;simpl.
                   rsimpl;lia.
                ** intro I2;apply IHN;auto.
                   apply pom_sizeb_order_subsumption in I2.
                   repeat rewrite <- clean_terms_sizeb in I2 by assumption.
                   lia.
          -- apply subs_eq;symmetry.
             apply var_split_hom;tauto.
          -- replace (bsp_box s) with (▢ s) in * by reflexivity.
             rewrite <- interpret_bsp_par in hyp.
             apply box_left_split_hom in hyp as (t&F&_).
             ++ discriminate.
             ++ assumption.
             ++ simpl;tauto.
          -- exfalso.
             apply order_subsumption_smaller in hyp.
             apply sizePomset_subsumption in hyp.
             rsimpl in hyp.
             rewrite <- interpret_bsp_par in hyp.
             rewrite <- interpret_bsp_size in hyp.
             rewrite <- interpret_bsp_unit in hyp.
             rewrite <- interpret_bsp_size in hyp.
             rsimpl in hyp.
             apply is_bsp_clean_bsp_size in C1;lia.
      + apply subs_eq.
        apply var_split_hom.
        tauto.
      + assert (Ct : is_bsp_clean (▢ t)) by apply C;clear C.
        pose proof (bsp_clean_eq s) as Es.
        rewrite Es.
        symmetry in Es.
        apply soundness_bsp_terms,order_subsumption_equiv in Es.
        rewrite <- Es in hyp.
        clear Es;revert hyp.
        destruct (bsp_clean_is_bsp_clean s) as [->|Cs];intro hyp.
        * apply subs_eq;symmetry.
          apply unit_split_hom;tauto.
        * apply box_right_split_hom in hyp;[|assumption|assumption].
          destruct hyp as (v&Ev&hyp).
          apply IHN in hyp.
          -- rewrite Ev,hyp;reflexivity.
          -- lia.
          -- destruct t;(apply Ct)||(exfalso;apply Ct).
      + apply bsp_subs_eq,unit_split_hom;tauto.
  Qed.

  Lemma SP_Pomset_box_subsume s t f : box_homomorphism s t f -> SP_Pomset t -> SP_Pomset s.
  Proof.
    intros hf SP.
    cut (decOrder (fun a b : ⌊ s ⌋ => a ≤[ s] b));[intros D;split;auto|].
    - intros (e1&e2&e3&e4&(h1&h2&h3)&h4&h5&h6).
      apply sp_N_free.
      exists (f e1),(f e2),(f e3),(f e4).
        unfold independent in *.
        repeat rewrite <- (@box_Ord _ _ f hf).
        tauto.
    - split.
      + apply Well_nested_pat_WN.
        intros (e1&e2&e3&B1&B2&IB1&IB2&I1&I1'&I2&I2'&I3&I3').
        eapply Well_nested_pat_WN;[apply wf_wn|].
        exists (f e1),(f e2),(f e3).
        assert (IB1' : map f B1 ∈ map (map f) (Boxes s)) by (apply in_map_iff;exists B1;tauto).
        assert (IB2' : map f B2 ∈ map (map f) (Boxes s)) by (apply in_map_iff;exists B2;tauto).
        apply box_Boxes in IB1' as (B1'&IB1'&EB1').
        apply box_Boxes in IB2' as (B2'&IB2'&EB2').
        exists B1',B2'.
        repeat split;auto.
        * apply EB1',in_map_iff;exists e1;tauto.
        * rewrite <- EB2'.
          intro I;apply in_map_iff in I as (x&E&I).
          apply is_injective in E as ->;tauto.
        * apply EB1',in_map_iff;exists e2;tauto.
        * apply EB2',in_map_iff;exists e2;tauto.
        * rewrite <- EB1'.
          intro I;apply in_map_iff in I as (x&E&I).
          apply is_injective in E as ->;tauto.
        * apply EB2',in_map_iff;exists e3;tauto.
      + apply Left_atomic_pat_LAt;auto.
        intros (e1&e2&e3&B&IB&I1&I2&I3&h1&h2).
        eapply Left_atomic_pat_LAt;[apply sp_dec|apply wf_la|].
        exists (f e1),(f e2),(f e3).
        assert (IB' : map f B ∈ map (map f) (Boxes s)) by (apply in_map_iff;exists B;tauto).
        apply box_Boxes in IB' as (B'&IB'&EB').
        exists B'.
        repeat split;auto.
        * rewrite <- EB'.
          intro I;apply in_map_iff in I as (x&E&I).
          apply is_injective in E as ->;tauto.
        * apply EB',in_map_iff;exists e2;tauto.
        * apply EB',in_map_iff;exists e3;tauto.
        * rewrite <- (@box_Ord _ _ f);auto.
        * rewrite <- (@box_Ord _ _ f);auto.
      + apply Right_atomic_pat_RAt;auto.
        intros (e1&e2&e3&B&IB&I1&I2&I3&h1&h2).
        eapply Right_atomic_pat_RAt;[apply sp_dec|apply wf_ra|].
        exists (f e1),(f e2),(f e3).
        assert (IB' : map f B ∈ map (map f) (Boxes s)) by (apply in_map_iff;exists B;tauto).
        apply box_Boxes in IB' as (B'&IB'&EB').
        exists B'.
        repeat split;auto.
        * rewrite <- EB'.
          intro I;apply in_map_iff in I as (x&E&I).
          apply is_injective in E as ->;tauto.
        * apply EB',in_map_iff;exists e2;tauto.
        * apply EB',in_map_iff;exists e3;tauto.
        * rewrite <- (@box_Ord _ _ f);auto.
        * rewrite <- (@box_Ord _ _ f);auto.
    - intros a b.
      case_prop (f a ≤[t] f b).
      + left.
        rewrite (@box_Ord _ _ f);auto.
      + right.
        rewrite (@box_Ord _ _ f);auto.
  Qed.
      
  Theorem completeness_subsumption : forall s t : bsp_terms X, s ⊑ t <-> ⟦ s ⟧ ⊑ ⟦ t ⟧.
  Proof.
    intros s t;split;[apply subsume_sound|].
    intros E.
    apply subsumption_is_box_then_order in E as (U&E1&E2).
    assert (exists u, U ≃ ⟦u⟧) as (u&Eu).
    - apply bsp_pomsets_iff_SP_Pomset.
      destruct E1 as (f&hf).
      cut (SP_Pomset U);[intro e;exists e;tauto|].
      apply (SP_Pomset_box_subsume _ _ f hf),bsp_pomsets_SP_pomsets.
    - rewrite (box_subsumption_equiv _ _ Eu) in E1.
      symmetry in Eu.
      rewrite <- (order_subsumption_equiv _ _ Eu) in E2.
      clear U Eu.
      transitivity u.
      + apply completeness_box_hom,E1.
      + apply completeness_order_hom,E2.
  Qed.
End s.