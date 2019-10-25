Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools Bool.

Notation ϒ := unit.
Notation υ := tt.

Inductive bintree : Set := leaf : bool -> bintree | node : bintree -> bintree -> bintree.

Notation " 𝟣 " := (leaf true).
Notation " 𝟢 " := (leaf false).
Infix " ⊎ " := node (at level 40).

Fixpoint type (t : bintree) : Set :=
  match t with
  | 𝟣 => ϒ
  | 𝟢 => False
  | t1 ⊎ t2 => type t1 + type t2
  end.

Notation " ⟨ t ⟩ " := (type t).

Fixpoint domain (t : bintree) : list ⟨t⟩ :=
  match t with
  | 𝟣 => [υ]
  | 𝟢 => []
  | t1 ⊎ t2 => map inl (domain t1) ++ map inr (domain t2)
  end.

Notation " ⟪ t ⟫ " := (domain t).
Definition 𝒫 t := subsets ⟪t⟫.

Global Instance size_type : Size bintree := fun t => ⎢⟪t⟫⎥.

Remark size_leaf_true : ⎢𝟣⎥ = 1.
Proof. reflexivity. Qed.
Remark size_leaf_false : ⎢𝟢⎥ = 0.
Proof. reflexivity. Qed.
Remark size_node s t : ⎢s ⊎ t⎥ = ⎢s⎥+⎢t⎥.
Proof. unfold size,size_type;rsimpl; reflexivity. Qed.
Hint Rewrite size_leaf_true size_leaf_false size_node : simpl_rewrite.

Lemma domain_nodup t : NoDup ⟪t⟫.
Proof.
  induction t as [[]|];simpl.
  - apply NoDup_cons;[simpl;tauto|].
    apply NoDup_nil.
  - apply NoDup_nil.
  - apply NoDup_app.
    + intros [];repeat rewrite in_map_iff;intros (b&<-&Ib) (c&F&Ic);discriminate.
    + apply NoDup_map_injective,IHt1.
      split;intros x y E;inversion E;reflexivity.
    + apply NoDup_map_injective,IHt2.
      split;intros x y E;inversion E;reflexivity.
Qed.

Lemma domain_spec t x : x ∈ ⟪t⟫.
Proof.
  revert x;induction t as [[]|];simpl.
  - intros [];simpl;tauto.
  - intro a;apply a.
  - intros [x|x];apply in_app_iff;[left|right];apply in_map_iff;exists x;intuition.
Qed.
Hint Resolve domain_spec.

Corollary domain_incl t l : l ⊆ ⟪t⟫.
Proof. intros x _;auto. Qed.
Hint Resolve domain_incl.

Lemma domain_equiv t l : ⟪t⟫ ⊆ l -> ⟪t⟫ ≈ l.
Proof. intros h;apply antisymmetry;[apply h|auto]. Qed.

Lemma 𝒫_spec t l : exists m, m ∈ 𝒫 t /\ l ≈ m.
Proof. apply subsets_spec;auto. Qed.

Lemma 𝒫_NoDup t l : l ∈ 𝒫 t -> NoDup l.
Proof. apply subsets_NoDup,domain_nodup. Qed.
Hint Resolve 𝒫_NoDup.

Global Instance decidable_type t : decidable_set ⟨t⟩.
Proof.
  induction t as [[]|].
  - apply Build_decidable_set with (eqX := fun _ _ => true).
    intros [] [];apply ReflectT;reflexivity.
  - apply Build_decidable_set with (eqX := fun _ _ => false).
    intros [].
  - simpl;apply dec_sum;assumption.
Qed.

Definition complement t (D : list ⟨t⟩) := (fun e => negb (inb e D)):> ⟪t⟫.
Notation " ¬ " := complement.

Lemma complement_spec t (e : ⟨t⟩) D : ~ e ∈ D <-> e ∈ ¬ D.
Proof. unfold complement;rewrite filter_In,negb_true_iff,inb_false;split;auto||tauto. Qed.

Lemma NoDup_complement t (D : list ⟨t⟩): NoDup (¬D).
Proof. apply filter_NoDup,domain_nodup. Qed.

Global Instance complement_proper {t} :
  Proper (@equivalent ⟨t⟩ ==> @equivalent ⟨t⟩) (@complement t).
Proof. intros l m E e;rewrite <- complement_spec,E,complement_spec;reflexivity. Qed.

Lemma complement_nil t : ¬ [] ≈ ⟪t⟫.
Proof. intro e;rewrite <- complement_spec;simpl;split;auto. Qed.
Lemma complement_full t : ¬ ⟪t⟫ ≈ [].
Proof. intro e;rewrite <- complement_spec;simpl;split;auto. Qed.

(** * Decidable propositions *)
Class DecidableProp (P : Prop) := dec_prop: {P} + {~ P}.
Arguments dec_prop : clear implicits.
Arguments dec_prop P {DecidableProp}.

Ltac case_prop p :=
  let D := fresh "D" in
  let hyp := fresh "hyp" in
  destruct (dec_prop p) as [hyp|hyp].

Global Instance DecidableProp_Eq (A : Set) (x y : A) :
  decidable_set A -> DecidableProp (x=y).
Proof. intro;destruct_eqX x y;[left;reflexivity|right;assumption]. Qed.
Global Instance DecidableProp_In (A : Set) (x : A) l :
  decidable_set A -> DecidableProp (x ∈ l).
Proof. intro;case_in x l;[left|right];assumption. Qed.
Global Instance DecidableProp_Incl (A : Set) (l m : list A) :
  decidable_set A -> DecidableProp (l ⊆ m).
Proof.
  intro;case_eq (inclb l m);intro h;[left|right];
    revert h;[|rewrite <- not_true_iff_false];rewrite inclb_correct;tauto.
Qed.
Global Instance DecidableProp_Equiv (A : Set) (l m : list A) :
  decidable_set A -> DecidableProp (l ≈ m).
Proof.
  intro;case_eq (equivalentb l m);intro h;[left|right];
    revert h;[|rewrite <- not_true_iff_false];rewrite equivalentb_spec;tauto.
Qed.

Definition test (p : Prop) {d : DecidableProp p} : bool :=
  if (dec_prop p) then true else false.

Arguments test p {d}.

Lemma test_reflect p `{DecidableProp p} : reflect p (test p).
Proof. unfold test;case_prop p;[apply ReflectT|apply ReflectF];assumption. Qed.

Global Instance DecidableProp_neg p : DecidableProp p -> DecidableProp (~p).
Proof. intro D;case_prop p;[right|left];tauto. Qed.
  
Global Instance DecidableProp_conj p1 p2 :
  DecidableProp p1 -> DecidableProp p2 -> DecidableProp (p1 /\ p2).
Proof. intros D1 D2;case_prop p1;case_prop p2;(left;tauto)||(right;tauto). Qed.

Global Instance DecidableProp_disj p1 p2 :
  DecidableProp p1 -> DecidableProp p2 -> DecidableProp (p1 \/ p2).
Proof. intros D1 D2;case_prop p1;case_prop p2;(left;tauto)||(right;tauto). Qed.

Global Instance DecidableProp_impl p1 p2 :
  DecidableProp p1 -> DecidableProp p2 -> DecidableProp (p1 -> p2).
Proof. intros D1 D2;case_prop p1;case_prop p2;(left;tauto)||right;tauto. Qed.

Global Instance DecidableProp_iff p1 p2 :
  DecidableProp p1 -> DecidableProp p2 -> DecidableProp (p1 <-> p2).
Proof. intros D1 D2;case_prop p1;case_prop p2;(left;tauto)||right;tauto. Qed.

Global Instance DecidableProp_forall_bnd (A : Set) p l :
  (forall a : A, DecidableProp (p a)) -> 
  DecidableProp (forall a, a ∈ l -> p a).
Proof.
  intros dp.
  case_eq (forallb (fun a => test (p a)) l);intro E;[left|right].
  - rewrite forallb_forall in E.
    intros a Ia.
    apply E in Ia.
    rewrite reflect_iff by apply test_reflect.
    assumption.
  - apply forallb_false_exists in E as (a&Ia&Fa).
    intros h;apply h in Ia.
    rewrite reflect_iff in Ia by apply test_reflect.
    rewrite Ia in Fa;discriminate.
Qed.

Global Instance DecidableProp_exists_bnd (A : Set) p l :
  (forall a : A, DecidableProp (p a)) -> DecidableProp (exists a, a ∈ l /\ p a).
Proof.
  intros dp.
  case_eq (existsb (fun a => test (p a)) l);intro E;[left|right].
  - apply existsb_exists in E as (a&Ia&Pa).
    rewrite <- reflect_iff in Pa by apply test_reflect.
    exists a;tauto.
  - intros (a&Ia&Pa);apply not_true_iff_false in E;apply E,existsb_exists.
    exists a;split;[assumption|].
    rewrite <- reflect_iff by apply test_reflect.
    assumption.
Qed.

Global Instance DecidableProp_forall_fn t p :
  (forall x : ⟨t⟩, DecidableProp (p x)) -> DecidableProp (forall x, p x).
Proof.
  intro D;case_prop (forall x, x ∈ ⟪t⟫ -> p x);[left|right].
  - intros x;apply hyp;auto.
  - intros h;apply hyp;intros x Ix;apply h.
Qed.
  
Global Instance DecidableProp_exists_fn t p :
  (forall x : ⟨t⟩, DecidableProp (p x)) -> DecidableProp (exists x, p x).
Proof.
  intro D;case_prop (exists x, x ∈ ⟪t⟫ /\ p x);[left|right].
  - destruct hyp as (x&Ix&Px);exists x;assumption.
  - intros (x&Px);apply hyp;exists x;split;auto.
Qed.

Global Instance DecidableProp_equiv_prop p q :
  DecidableProp p -> (p <-> q) -> DecidableProp q.
Proof. intros D E;case_prop p;[left|right];rewrite <- E;assumption. Qed.

Ltac prove_proper :=
  match goal with
  | _ : _ |- Proper ((@equivalent _) ==> iff) _ =>
    let l := fresh "l" in
    let m := fresh "m" in
    let E := fresh "E" in
    intros l m E;setoid_rewrite E;reflexivity
  end.

Lemma bounded_universal_quantification t p :
  Proper ((@equivalent _) ==> iff) p -> (forall x, x ∈ 𝒫 t -> p x) <-> (forall x, p x).
Proof.
  intros E;split;[|intuition].
  intros h x; destruct (𝒫_spec x) as (l&I&->).
  apply h,I.
Qed.

Lemma bounded_existantial_quantification t p :
  Proper ((@equivalent _) ==> iff) p -> (exists x, x ∈ 𝒫 t /\ p x) <-> (exists x, p x).
Proof.
  intros E;split;[firstorder|].
  intros (x&hx); destruct (𝒫_spec x) as (y&Iy&Ey).
  setoid_rewrite Ey in hx;exists y;tauto.
Qed.

Ltac simpl_quantif :=
  repeat (setoid_rewrite bounded_universal_quantification;[|prove_proper])
  || (setoid_rewrite bounded_existantial_quantification;[|prove_proper]).
Tactic Notation "simpl_quantif" "in" hyp(h) :=
  repeat (setoid_rewrite bounded_universal_quantification in h;[|prove_proper])
  || (setoid_rewrite bounded_existantial_quantification in h;[|prove_proper]).

Lemma dec_prop_set t p : (forall x : ⟨t⟩, DecidableProp (p x)) -> { l | forall e, e ∈ l <-> p e}.
Proof.
  intro h;exists ((fun x => test (p x)) :> ⟪t⟫);intro e.
  rewrite filter_In,<- reflect_iff by apply test_reflect;intuition auto.
Qed.

Lemma dec_prop_powerset t p :
  (forall x : list ⟨t⟩, DecidableProp (p x)) -> { l | forall e, e ∈ 𝒫 t -> e ∈ l <-> p e}.
Proof.
  intros D;exists ((fun x => test (p x)) :> 𝒫 t);intro e.
  rewrite filter_In,<- reflect_iff by apply test_reflect;intuition auto.
Qed.

Lemma dec_prop_powerset_bnd t p L :
  (forall x : list ⟨t⟩, DecidableProp (p x)) -> {l | forall e, e ∈ l <-> e ∈ L /\ p e}.
Proof.
  intros D;exists ((fun x => test (p x)) :> L);intro e.
  rewrite filter_In,<- reflect_iff by apply test_reflect;intuition auto.
Qed.

(** * Injective, surjective and bijective functions over finite types. *)
Global Instance decidable_injective s t (f : ⟨s⟩ -> ⟨t⟩) : DecidableProp (injective f).
Proof.
  eapply DecidableProp_equiv_prop;[|split;[intro h;split;apply h|intros [h];apply h]].
  typeclasses eauto.
Qed.

Global Instance decidable_surjective s t (f : ⟨s⟩ -> ⟨t⟩) : DecidableProp (surjective f).
Proof.
  eapply DecidableProp_equiv_prop;[|split;[intro h;split;apply h|intros [h];apply h]].
  typeclasses eauto.
Qed.

Global Instance decidable_bijective s t (f : ⟨s⟩ -> ⟨t⟩) :  DecidableProp (bijective f).
Proof.
  case_prop (injective f);[case_prop (surjective f);[left;split;assumption|]|];
    right;intros [I S];tauto.
Qed.

Lemma injective_inverse s t (f : ⟨s⟩ -> ⟨t⟩) :
  injective f -> { g | (forall a, g (f a) = Some a) /\ forall a b, g b = Some a -> f a = b }.
Proof.
  intros I.
  set (g' := fun b => (fun a => f a =?= b) :> ⟪s⟫).
  set (g := fun b => match g' b with a::_ => Some a | _ => None end).
  exists g;split.
  - intros a;unfold g,g'.
    case_eq ((fun a0 : ⟨s⟩ => f a0 =?= f a) :> ⟪s⟫).
    + intro F;exfalso.
      cut (a ∈ []);[intro FF;apply FF|].
      rewrite <- F;clear F.
      simpl_In.
      rewrite eqX_correct.
      split;[apply domain_spec|reflexivity].
    + intros b ? E;f_equal.
      apply I.
      cut (b ∈ (b :: l));[|now left].
      rewrite <- E;clear E.
      simpl_In.
      rewrite eqX_correct.
      tauto.
  - intros a b;unfold g,g'.
    case_eq ((fun a0 : ⟨s⟩ => f a0 =?= b) :> ⟪s⟫);[discriminate|].
    intros c ? E ee;inversion ee;subst;clear ee.
    cut (a ∈ (a :: l));[|now left].
    rewrite <- E;clear E.
    simpl_In.
    rewrite eqX_correct.
    tauto.
Qed.

Lemma injective_inverse_iff s t (f : ⟨s⟩ -> ⟨t⟩) :
  injective f <-> exists g, (forall a, g (f a) = Some a) /\ forall a b, g b = Some a -> f a = b.
Proof.
  split;[intro I;destruct (injective_inverse I) as (g&hg);exists g;apply hg|].
  intros (g&h1&_).
  split;intros a b E.
  cut (Some a = Some b);[intros EE;inversion EE;reflexivity|].
  rewrite <- (h1 a),E, (h1 b);reflexivity.
Qed.

Lemma exists_unique_function_from_empty_type s :
  ⟪s⟫ = [] -> forall t, { f : ⟨s⟩ -> ⟨t⟩ | forall g a, f a = g a }.
Proof.
  induction s as [[]|].
  - discriminate.
  - intros D t; exists (fun x : False => match x with end);intros g a.
    pose proof (domain_spec a) as F;exfalso;rewrite D in F;apply F.
  - simpl;intros D t.
    apply app_eq_nil in D as (D1&D2).
    apply map_eq_nil in D1.
    apply map_eq_nil in D2.
    destruct (IHs1 D1 t) as (f1&_).
    destruct (IHs2 D2 t) as (f2&_).
    exists (fun x => match x with inl y => f1 y | inr y => f2 y end);intros ? a.
    pose proof (@domain_spec (s1 ⊎ s2) a) as F;exfalso;simpl in *.
    rewrite D1,D2 in F;apply F.
Qed.

Lemma bijective_inverse s t (f : ⟨s⟩ -> ⟨t⟩) :
  bijective f -> { g | (forall a, g (f a) = a) /\ forall b, f (g b) = b }.
Proof.
  intros (I&S).
  cut (⟨s⟩ + {⟪s⟫ = [] /\ ⟪t⟫ = []}).
  - intros [a0|F].
    + destruct (injective_inverse I) as (g&h1&h2).
      set (g' := fun b => match g b with Some a => a | None => a0 end).
      exists g';split.
      * intro a;unfold g'.
         rewrite h1;reflexivity.
      * intros b;unfold g'.
         destruct (is_surjective b) as (a&<-).
         rewrite h1;reflexivity.
    + clear I S.
      destruct F as (F1&F2).
      destruct (exists_unique_function_from_empty_type F1 t) as (f'&_).
      destruct (exists_unique_function_from_empty_type F2 s) as (g'&_).
      exists g';split;intros a;pose proof (domain_spec a) as F;exfalso;
        [rewrite F1 in F|rewrite F2 in F];apply F.
  - case_eq ⟪s⟫;[|intros a ? _;left;exact a].
    intros Ds;right;split;[reflexivity|].
    case_eq ⟪t⟫;[reflexivity|].
    intros b ? _;exfalso.
    destruct (is_surjective b) as (a&_).
    cut (a ∈ []);[intro F;apply F|].
    rewrite <- Ds;apply domain_spec.
Qed.

Definition inverse { s t } (f : ⟨s⟩ -> ⟨t⟩) {b : bijective f} :=
  proj1_sig (bijective_inverse b).
Arguments inverse : clear implicits.
Arguments inverse { s t } f { b }.
Notation " f ̃ " := (inverse f) (at level 0).

Lemma inverse_compose_id1 { s t } (f : ⟨s⟩ -> ⟨t⟩) {b : bijective f} : f ̃ ∘ f ≃ id.
Proof.
  unfold inverse;destruct (bijective_inverse b) as (g&(h1&h2));simpl;intro x;apply h1.
Qed.
Lemma inverse_compose_id2 { s t } (f : ⟨s⟩ -> ⟨t⟩) {b : bijective f} : f ∘ (f ̃) ≃ id.
Proof.
  unfold inverse;destruct (bijective_inverse b) as (g&(h1&h2));simpl;intro;apply h2.
Qed.

Lemma inverse_elim1 { s t } (f : ⟨s⟩ -> ⟨t⟩) {b : bijective f} x : f ̃ (f x) = x.
Proof.
  unfold inverse;destruct (bijective_inverse b) as (g&(h1&h2));simpl;apply h1.
Qed.
Lemma inverse_elim2 { s t } (f : ⟨s⟩ -> ⟨t⟩) {b : bijective f} x : f (f ̃ x) = x.
Proof.
  unfold inverse;destruct (bijective_inverse b) as (g&(h1&h2));simpl;apply h2.
Qed.

Lemma bijective_inverse_iff s t (f : ⟨s⟩ -> ⟨t⟩) :
  bijective f <-> exists g, (forall a, g (f a) = a) /\ forall b, f (g b) = b.
Proof.
  split;[intro B;exists (f ̃);split;[apply inverse_compose_id1|apply inverse_compose_id2]|].
  intros (g&h1&h2);split;split.
  - intros x y E;rewrite <- (h1 x),E,h1;reflexivity.
  - intros y;exists (g y);apply h2.
Qed.

Lemma is_injective_sequiv {A B} (f : A -> B) :
  injective f -> forall C, forall g h : C -> A, f ∘ g ≃ f ∘ h -> g ≃ h .
Proof. intros Inj C g h E x;apply is_injective,E. Qed.
                                              
Lemma inverse_unique s t (ϕ : ⟨s⟩ -> ⟨t⟩) `{bijective _ _ ϕ}:
  forall ψ, (ϕ ∘ ψ ≃ id) -> ψ ≃ ϕ ̃.
Proof.
  intros ψ h.
  eapply is_injective_sequiv;[apply H|].
  rewrite h,inverse_compose_id2;reflexivity.
Qed.

Lemma inverse_compose s t u ϕ ψ `{bijective ⟨s⟩ ⟨t⟩ ϕ} `{bijective ⟨t⟩ ⟨u⟩ ψ} :
  (ψ ∘ ϕ)̃ ≃ ϕ ̃ ∘ ψ ̃.
Proof.
  symmetry;apply inverse_unique.
  transitivity (ψ ∘ (ϕ ∘ (ϕ) ̃) ∘ (ψ) ̃);[repeat rewrite compose_assoc;reflexivity|].
  rewrite inverse_compose_id2,compose_id_r,inverse_compose_id2;reflexivity.
Qed.

Lemma inverse_proper s t ϕ ψ `{bijective ⟨s⟩ ⟨t⟩ ϕ} `{bijective ⟨s⟩ ⟨t⟩ ψ} :
  ϕ ≃ ψ -> ϕ ̃ ≃ ψ ̃.
Proof.
  intros E;apply inverse_unique.
  rewrite <- E,inverse_compose_id2;reflexivity.
Qed.

Global Instance inverse_bijective s t ϕ `{bijective ⟨s⟩ ⟨t⟩ ϕ} : bijective (ϕ ̃).
Proof.
  apply bijective_inverse_iff;exists ϕ;split;[apply inverse_compose_id2
                                        |apply inverse_compose_id1].
Qed.

Lemma inverse_id s : (@id ⟨s⟩) ̃ ≃ id.
Proof. symmetry;apply inverse_unique;reflexivity. Qed.
      
Lemma inverse_involutive s t ϕ `{bijective ⟨s⟩ ⟨t⟩ ϕ} : ϕ ̃ ̃ ≃ ϕ.
Proof. symmetry;apply inverse_unique,inverse_compose_id1. Qed.

Lemma inverse_eq_iff s t ϕ `{bijective ⟨s⟩ ⟨t⟩ ϕ} x y : ϕ ̃ x = y <-> x = ϕ y.
Proof.
  split;intro;subst;[symmetry;apply inverse_compose_id2
                    |apply (inverse_compose_id1 y)].
Qed.
  
Lemma injective_size s t (f : ⟨s⟩ -> ⟨t⟩) : injective f -> ⎢s⎥ <= ⎢t⎥.
Proof.
  intros I.
  unfold size,size_type.
  transitivity ⎢map f ⟪s⟫⎥;[rsimpl;reflexivity|].
  apply NoDup_incl_length.
  - apply NoDup_map_injective,domain_nodup;assumption.
  - intros ? _;apply domain_spec.
Qed.
Lemma surjective_size s t (f : ⟨s⟩ -> ⟨t⟩) : surjective f -> ⎢t⎥ <= ⎢s⎥.
Proof.
  intros I.
  unfold size,size_type.
  transitivity ⎢map f ⟪s⟫⎥;[|rsimpl;reflexivity].
  apply NoDup_incl_length.
  - apply domain_nodup.
  - intros ? _;apply in_map_iff.
    destruct (is_surjective a) as (b&<-).
    exists b;split;[reflexivity|apply domain_spec].
Qed.

Corollary bijective_size s t (f : ⟨s⟩ -> ⟨t⟩) : bijective f -> ⎢t⎥ = ⎢s⎥.
Proof.
  intros (h1&h2);apply antisymmetry;[eapply surjective_size|eapply injective_size];
    eassumption.
Qed.

Lemma injective_size_bijective s t (f : ⟨s⟩ -> ⟨t⟩) :
  injective f -> ⎢t⎥ <= ⎢s⎥ -> bijective f.
Proof.
  intros I len;split;[assumption|].
  case_eq (forallb (fun a => existsb (fun b => f b =?= a) ⟪s⟫)
                   ⟪t⟫);intro E.
  - revert E.
    rewrite forallb_forall.
    setoid_rewrite existsb_exists.
    setoid_rewrite eqX_correct.
    intros E;split.
    intros y;destruct (E y) as (x&_&<-).
    + apply domain_spec.
    + exists x;reflexivity.
  - revert E.
    rewrite forallb_false_exists.
    intros (a&Ia&E).
    apply not_true_iff_false in E.
    rewrite existsb_exists in E.
    setoid_rewrite eqX_correct in E.
    pose proof (map_length f ⟪s⟫) as F.
    exfalso.
    cut (S ⎢s⎥ <= ⎢t⎥);[revert len;clear;lia|].
    transitivity (⎢a :: rm a (map f ⟪s⟫)⎥).
    + rsimpl.
      rewrite rm_notin;[rsimpl;reflexivity|].
      rewrite in_map_iff;intros (b&<-&Ib);apply E;exists b;tauto.
    + apply NoDup_incl_length.
      * apply NoDup_cons.
        -- rewrite rm_In;tauto.
        -- apply filter_NoDup,NoDup_map_injective,domain_nodup;apply I.
      * intros ? _;apply domain_spec.
Qed.

Lemma surjective_size_bijective s t (f : ⟨s⟩ -> ⟨t⟩) :
  surjective f -> ⎢s⎥ <= ⎢t⎥ -> bijective f.
Proof.
  intros hS len;split;[|assumption].
  case_eq (existsb (fun a => existsb (fun b => negb (a =?= b) && f a =?= f b) ⟪s⟫)
                   ⟪s⟫);intro E. 
  - exfalso;revert E.
    rewrite existsb_exists.
    setoid_rewrite existsb_exists.
    setoid_rewrite andb_true_iff.
    setoid_rewrite negb_true_iff.
    setoid_rewrite eqX_false.
    setoid_rewrite eqX_correct.
    intros (x&Ix&y&Iy&N&E).
    cut (⎢ x :: ⟪s⟫ ∖ x ⎥ <= ⎢map f (⟪s⟫ ∖ x) ⎥);[clear;rsimpl;lia|].
    transitivity ⎢t⎥.
    + rewrite <- len.
      apply NoDup_incl_length.
      * apply NoDup_cons.
        -- rewrite rm_In;tauto.
        -- apply filter_NoDup,domain_nodup.
      * rewrite <- rm_equiv by assumption;reflexivity.
    + apply NoDup_incl_length.
      * apply domain_nodup.
      * intros a _;apply in_map_iff;destruct (is_surjective a) as (b&<-).
        destruct_eqX x b;subst.
        -- exists y;split;[symmetry;assumption|].
           apply rm_In;split;[apply domain_spec|assumption].
        -- exists b;split;[reflexivity|].
           apply rm_In;split;[apply domain_spec|assumption].
  - split;intros x y Exy;destruct_eqX x y;[reflexivity|exfalso].
    apply not_true_iff_false in E;apply E.
    rewrite existsb_exists;setoid_rewrite existsb_exists.
    setoid_rewrite andb_true_iff.
    setoid_rewrite negb_true_iff.
    setoid_rewrite eqX_false.
    setoid_rewrite eqX_correct.
    exists x;split;[apply domain_spec|].
    exists y;split;[apply domain_spec|].
    tauto.  
Qed.
Corollary endofunction_injective_iff_bijective s (f : ⟨s⟩ -> ⟨s⟩) :
  injective f <-> bijective f.
Proof. split;intro h;[apply injective_size_bijective;[|reflexivity]|];apply h. Qed.
Corollary endofunction_surjective_iff_bijective s (f : ⟨s⟩ -> ⟨s⟩) :
  surjective f <-> bijective f.
Proof. split;intro h;[apply surjective_size_bijective;[|reflexivity]|];apply h. Qed.

(** * Pre-Image *)

Remark preimage_dec {s t} (f : ⟨s⟩ -> ⟨t⟩) l a : DecidableProp (exists b, b ∈ l /\ f a = b).
Proof. typeclasses eauto. Qed.

Definition preimage {s t} (f : ⟨s⟩ -> ⟨t⟩) l :=
  proj1_sig (dec_prop_set (preimage_dec f l)).

Notation " f ¯¹ " := (preimage f) (at level 40).

Lemma preimage_spec {s t} (f : ⟨s⟩ -> ⟨t⟩) l a :
  a ∈  f ¯¹ l <-> exists b, b ∈ l /\ f a = b.
Proof. unfold preimage;destruct (dec_prop_set _) as (L&hL);simpl;apply hL. Qed.

Lemma preimage_inverse s t f `{bijective ⟨s⟩ ⟨t⟩ f} l : f ¯¹ l ≈ map (f ̃) l.
Proof.
  intro a;rewrite preimage_spec,in_map_iff.
  setoid_rewrite inverse_eq_iff.
  setoid_rewrite and_comm at 2.
  assert (E: forall x y : ⟨t⟩, x = y <-> y = x) by (firstorder subst;reflexivity).
  setoid_rewrite E at 1;reflexivity.
Qed.
  
                                                              

(** * Correspondance with lists. *)

Fixpoint bintree_of_nat n :=
  match n with
  | 0 => 𝟢
  | S n => 𝟣 ⊎ (bintree_of_nat n)
  end.

Lemma bintree_of_nat_size n : ⎢ bintree_of_nat n ⎥ = n.
Proof. induction n;[|rsimpl;rewrite size_node,IHn;simpl];reflexivity. Qed.

Definition 𝒯 {A} (l : list A) := (bintree_of_nat ⎢l⎥).
Fixpoint 𝒯e {A : Set} (l : list A) : ⟨𝒯 l⟩ -> A :=
  match l with
  | [] => fun x : False => match x with end
  | a::l => fun x => match x with inl _ => a | inr y => @𝒯e A l y end
  end.
Notation 𝒯l l := (@𝒯e _ l).

Lemma translation_internal {A:Set} (l : list A) (a : ⟨𝒯 l⟩) : 𝒯e a ∈ l.
Proof. revert a;induction l;intros [];simpl;intuition. Qed.

Lemma translation_invert {A:Set} `{decidable_set A} (l : list A) a :
  a ∈ l -> { b : ⟨𝒯 l⟩ | 𝒯e b = a}.
Proof.
  revert a;induction l;simpl.
  - tauto.
  - intros b.
    destruct_eqX a b.
    + intros _;exists (inl υ);reflexivity.
    + case_in b l.
      * intros _;destruct (IHl b I) as (c&<-).
        exists (inr c);reflexivity.
      * intros F;exfalso.
        apply I;destruct F as [->|F];tauto.
Qed.

Lemma translation_total {A:Set} (l : list A) a : a ∈ l -> exists b : ⟨𝒯 l⟩, 𝒯e b = a.
Proof.
  revert a;induction l;simpl.
  - tauto.
  - intros b [<-|Ib].
    + exists (inl υ);reflexivity.
    + destruct (IHl b Ib) as (c&<-).
      exists (inr c);reflexivity.
Qed.

Lemma translation_injective {A : Set} (l : list A) :
  NoDup l -> injective (𝒯l l).
Proof.
  induction l;simpl.
  - split;intros _ [].
  - intros ND;apply NoDup_cons_iff in ND as (nI&ND).
    pose proof (IHl ND) as ih;clear IHl.
    split;intros [[]|] [[]|].
    + reflexivity.
    + intros ->;exfalso;apply nI,translation_internal.
    + intros <-;exfalso;apply nI,translation_internal.
    + intros E;apply ih in E as ->;reflexivity.
Qed.

Lemma incl_set_pred_make_function {A B : Set} (l : list (list A)) (m : list (list B)) f :
  injective f -> NoDupEq l -> map (map f) l ≲ m ->
  exists g : ⟨𝒯 l⟩ -> ⟨𝒯 m⟩, (forall x, map f (𝒯e x) ≈ 𝒯e (g x)) /\ injective g.
Proof.
  intro Inj;induction l.
  - intros _ _;exists (fun x : False => match x with end).
    split;[|split];intros [].
  - intros (nI&ND).
    intros hyp.
    destruct (IHl ND) as (g&hg&Ig).
    + intros b Ib;apply hyp;right;apply Ib.
    + destruct (hyp (map f a)) as (b&Ib&Eb);[now left|].
      destruct (translation_total Ib) as (k&<-).
      case_in k (map g ⟪𝒯 l⟫).
      * exfalso.
        apply in_map_iff in I as (t&<-&It).
        rewrite <- hg in Eb.
        apply (nI _ (translation_internal t)).
        intros x;split.
        -- intros Ix;cut (f x ∈ map f a);[rewrite Eb|];rewrite in_map_iff.
           ++ intros (y&E&Iy);apply Inj in E as ->;assumption.
           ++ exists x;tauto.
        -- intros Ix;cut (f x ∈ map f (𝒯e t));[rewrite <- Eb|];
             rewrite in_map_iff.
           ++ intros (y&E&Iy);apply Inj in E as ->;assumption.
           ++ exists x;tauto.
      * exists (fun x => match x with inl _ => k | inr y => g y end).
        split.
        -- intros [[]|].
           ++ simpl;assumption.
           ++ rewrite <- hg;simpl;reflexivity.
        -- split;intros [[]|] [[]|].
           ++ reflexivity.
           ++ intros -> ;exfalso;apply I,in_map_iff;exists t;split;auto.
           ++ intros <- ;exfalso;apply I,in_map_iff;exists t;split;auto.
           ++ intro;f_equal;apply Ig;assumption.
Qed.

(** * Fixpoints *)
Section fixpoints.
  Context {t : bintree} {f : ⟨t⟩ -> ⟨t⟩} {a : ⟨t⟩}.

  Definition iterator i := map (fun k => iter_fun f k a) (seq 0 (S i)).

  Notation Ω := iterator.
  
  Lemma iterator_spec : forall n x, x ∈ Ω n <-> exists m, m <= n /\ x = iter_fun f m a.
  Proof.
    intros n x;unfold Ω.
    rewrite in_map_iff.
    setoid_rewrite in_seq;simpl.
    split;intros (k&E1&E2);subst;exists k;split;reflexivity||lia.
  Qed.

  Lemma iterator_Sn : forall n, Ω (S n) = Ω n ++[iter_fun f (S n) a].
  Proof.
    intro n;unfold Ω.
    replace (S (S n)) with (S n + 1) by lia.
    cut (forall k s, seq s (k + 1) = seq s k ++ [s+k]).
    - intros ->;rewrite map_app;reflexivity.
    - clear;intro k;induction k;[intro s;simpl;f_equal;lia|].
      intros s;simpl;rewrite IHk;f_equal;f_equal;f_equal;lia.
  Qed.

  Lemma iterator_incr k :  iter_fun f (S k) a ∈ Ω k \/ ⎢{{Ω (S k)}}⎥ = S (S k). 
  Proof.
    induction k.
    - simpl;unfold Basics.compose,id;simpl.
      destruct_eqX a (f a);simpl;auto.
      repeat rewrite <- E;auto.
    - destruct IHk as [ih|ih].
      + left;rewrite iterator_Sn.
        rewrite in_app_iff.
        apply iterator_spec in ih as (m&Im&E).
        destruct_eqX k m.
        * right;left.
          simpl in *;unfold Basics.compose in *.
          repeat rewrite E;reflexivity.
        * left;apply iterator_spec;exists (S m).
          split;[lia|].
          simpl in *;unfold Basics.compose in *.
          repeat rewrite E;reflexivity.
      + case_in (iter_fun f (S (S k)) a) (Ω (S k));[tauto|].
        right.
        rewrite iterator_Sn.
        replace {{Ω (S k) ++ [iter_fun f (S (S k)) a]}}
          with ({{Ω (S k)}}++ [iter_fun f (S (S k)) a]);
          [rsimpl in *;rewrite ih;simpl;lia|].
        revert I;generalize (iter_fun f (S (S k)) a);
          generalize (Ω (S k));clear.
        intro l;induction l;simpl.
        * reflexivity.
        * intros b Nb.
          case_in a {{l}};case_in a {{l++[b]}}.
          -- apply IHl;tauto.
          -- exfalso;apply I0;simpl_In in *;tauto.
          -- exfalso;apply I;simpl_In in *;simpl in I0.
             firstorder subst;tauto.
          -- simpl;rewrite IHl;[reflexivity|tauto].
  Qed.

  Corollary exists_max_iterator : exists k, iter_fun f (S k) a ∈ Ω k.
  Proof.
    destruct (iterator_incr ⎢ t ⎥) as [E|FF].
    - exists ⎢t⎥;assumption.
    - exfalso;cut (⎢ {{Ω (S ⎢t⎥)}} ⎥ <= ⎢t⎥);[lia|].
      apply NoDup_incl_length;[apply NoDup_undup|auto].
  Qed.

  Proposition exists_iterates_list : exists L, forall x, (exists n, iter_fun f n a = x) <-> x ∈ L.
  Proof.
    destruct exists_max_iterator as (k&Ek).
    exists (Ω k);split.
    - intros (n&<-).
      induction n.
      + apply iterator_spec;exists 0;split;[lia|reflexivity].
      + apply iterator_spec in IHn as (m&Im&E).
        apply Nat.succ_le_mono in Im.
        apply Nat.le_succ_r in Im as [Im|Im].
        * apply iterator_spec;exists (S m);split;[assumption|].
          simpl;unfold Basics.compose;rewrite E;reflexivity.
        * inversion Im;subst.
          simpl;unfold Basics.compose;rewrite E;tauto.
    - rewrite iterator_spec;intros (n&_&->);exists n;reflexivity.
  Qed.

  Theorem exists_loop : exists n m, n < m /\ iter_fun f n a = iter_fun f m a.
  Proof.
    destruct exists_max_iterator as (k&Ik).
    apply iterator_spec in Ik as (m&hm&E).
    exists m,(S k);split;[lia|symmetry;assumption].
  Qed.
End fixpoints.

Theorem exists_uniform_fixpoint t (f : ⟨t⟩ -> ⟨t⟩) :
  injective f -> exists ω, forall a, iter_fun f (S ω) a = a.
Proof.
  intro Inj;cut (forall a b, f a = f b <-> a = b);
    [clear Inj;intro Inj|intros ? ?;split;[apply Inj|intros ->;reflexivity]].
  cut (exists N, forall a, a ∈ ⟪t⟫ -> iter_fun f (S N) a = a);
    [intros (N&hN);exists N;intro a;apply hN;auto|].
  cut (forall a, exists N, iter_fun f (S N) a = a).
  - intro hyp.
    induction ⟪t⟫.
    + exists 0;simpl;tauto.
    + destruct (hyp a) as (Na&Ea).
      destruct IHl as (Nl&El).
      exists ((S Na)*(S Nl)-1).
      replace (S((S Na)*(S Nl)-1)) with ((S Na)*(S Nl)).
      * intros b [<-|Ib].
        -- rewrite Nat.mul_comm,iter_fun_times.
           apply iter_fun_fix,Ea.
        -- rewrite iter_fun_times;apply iter_fun_fix,El,Ib.
      * simpl;lia.
  - intro a.
    destruct (@exists_loop _ f a) as (n&m&L&E).
    revert m L E;induction n;[intros [|m] L E;[lia|exists m;symmetry;apply E]|].
    intros [|m] L E;[lia|].
    simpl in E.
    unfold Basics.compose in E.
    rewrite Inj in E.
    apply (IHn m);lia||assumption.
Qed.
