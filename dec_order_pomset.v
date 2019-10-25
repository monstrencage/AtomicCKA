Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools algebra Bool relations.
Require Import pomsets.

Section s.
  Context {X:Set} {decX : decidable_set X}.
  Context {P : Pomset X} {decP : decOrder (fun x y => x ≤[P] y)}.
  
  Global Instance StrOrder_dec : forall x y, DecidableProp (x <[P] y).
  Proof. unfold strictOrd;typeclasses eauto. Qed.

  Global Instance Indep_dec : forall x y, DecidableProp (x ⫫[P] y).
  Proof. unfold independent;typeclasses eauto. Qed.

  Global Instance N_free_dec : DecidableProp (N_free P).
  Proof. unfold N_free;typeclasses eauto. Qed.
  
  Global Instance Well_nested_dec : DecidableProp (Well_nested P).
  Proof.
    unfold Well_nested.
    cut (DecidableProp (forall α,
                           α ∈ Boxes P ->
                           forall β, β ∈ Boxes P -> α ⊆ β \/ β ⊆ α \/ (forall a, ~ a ∈ α \/ ~ a ∈ β)));
      [|typeclasses eauto].
    intro h;apply (DecidableProp_equiv_prop h);clear;intuition.
  Qed.
  
  Global Instance Left_atomic_dec : DecidableProp (Left_atomic P).
  Proof.
    unfold Left_atomic.
    cut (DecidableProp
           (forall β,
               β ∈ Boxes P ->
               forall x, ~ x ∈ β -> forall a b : ⌊ P ⌋, a ∈ β -> b ∈ β -> x ≤[ P] a <-> x ≤[ P] b));
      [|typeclasses eauto].
    intro h;apply (DecidableProp_equiv_prop h);clear.
    split;intros h.
    - intros b x Ib;apply (h b Ib x).
    - intros b Ib x;apply (h b x Ib).
  Qed.
    
  Global Instance Right_atomic_dec : DecidableProp (Right_atomic P).
  Proof.
    unfold Right_atomic.
    cut (DecidableProp
           (forall β,
               β ∈ Boxes P ->
               forall x, ~ x ∈ β -> forall a b : ⌊ P ⌋, a ∈ β -> b ∈ β -> a ≤[ P] x <-> b ≤[ P] x));
      [|typeclasses eauto].
    intro h;apply (DecidableProp_equiv_prop h);clear.
    split;intros h.
    - intros b x Ib;apply (h b Ib x).
    - intros b Ib x;apply (h b x Ib).
  Qed.

  Global Instance WellFormed_dec : DecidableProp (WellFormed P).
  Proof.
    case_prop (Well_nested P);[|right;intros [? ? ?];tauto].
    case_prop (Left_atomic P);[|right;intros [? ? ?];tauto].
    case_prop (Right_atomic P);[|right;intros [? ? ?];tauto].
    left;split;assumption.
  Qed.
End s.

Section d.
  Context {X:Set} {decX : decidable_set X}.
  Context {P : Pomset X} {decP : decOrder (fun x y => x ≤[P] y)}.
  Context {Q : Pomset X} {decQ : decOrder (fun x y => x ≤[Q] y)}.

  (* Record LabelledBoxRelation := *)
  (*   { *)
  (*     carrier : bintree; *)
  (*     label : type (carrier) -> X; *)
  (*     order : relation (type carrier); *)
  (*     boxes : list (list (type carrier)) *)
  (*   }. *)

  (* Class Pomset := *)
  (*   { *)
  (*     rel :> LabelledBoxRelation; *)
  (*     po :> partialOrder (@order rel); *)
  (*     no_nil_box : ~ [] ∈ (boxes rel) *)
  (*   }. *)

  Global Instance check_iso (ϕ : ⌊Q⌋ -> ⌊P⌋) : DecidableProp (isomorphism ϕ).
  Proof.
    case_prop (bijective ϕ);[|right;intros [];tauto].
    case_prop ( forall a, ℓ (ϕ a) = ℓ a);[|right;intros [];tauto].
    case_prop  (forall a a', a ≤[ Q] a' <-> ϕ a ≤[ P] ϕ a');[|right;intros [];tauto].
    case_prop (map (map ϕ) (Boxes Q) ≃ Boxes P);[|right;intros [];tauto].
    left;split;assumption.
  Qed.
  
  Global Instance check_homo (ϕ : ⌊Q⌋ -> ⌊P⌋) : DecidableProp (homomorphism ϕ).
  Proof.
    case_prop (bijective ϕ);[|right;intros [];tauto].
    case_prop ( forall a, ℓ (ϕ a) = ℓ a);[|right;intros [];tauto].
    case_prop  (forall a a', a ≤[ Q] a' -> ϕ a ≤[ P] ϕ a');[|right;intros [];tauto].
    case_prop (map (map ϕ) (Boxes Q) ≲ Boxes P);[|right;intros [];tauto].
    left;split;assumption.
  Qed.
  
  Fixpoint list_of_functions s t : list (type s -> type t) :=
    match s with
    | leaf true => (map (fun v _ => v) (domain t))
    | leaf false => [(fun x : False => match x with end)]
    | node s1 s2 =>
      (flat_map (fun f1 => map (fun f2 x => match x with inl a => f1 a | inr b => f2 b end)
                            (list_of_functions s2 t))
                (list_of_functions s1 t))
    end.
  
  Lemma list_of_functions_spec (s t : bintree) :
    forall f : type s -> type t, exists g, g ∈ (list_of_functions s t) /\ f ≃ g.
  Proof.
    induction s as [[]|];simpl.
    - intros f.
      exists (fun _ => f υ);split.
      + apply in_map_iff;exists (f υ);split;[reflexivity|apply domain_spec].
      + intros [];reflexivity.
    - intros f;exists (fun x : False => match x with end);split;[now left|].
      intros [].
    - intros f.
      destruct (IHs1 (fun x => f (inl x))) as (g1&I1&E1).
      destruct (IHs2 (fun x => f (inr x))) as (g2&I2&E2).
      exists (fun x => match x with inl a => g1 a | inr b => g2 b end);split.
      + apply in_flat_map;exists g1;split;[assumption|].
        apply in_map_iff;exists g2;split;[|assumption].
        reflexivity.
      + intros [a|b];[apply E1|apply E2].
  Qed.

  Global Instance dec_subsumption : DecidableProp (P ⊑ Q).
  Proof.
    cut (DecidableProp
           (exists ϕ, ϕ ∈ (list_of_functions (PomType Q) (PomType P)) /\ homomorphism ϕ));
      [|typeclasses eauto].
    intro D;eapply DecidableProp_equiv_prop;[apply D|clear D].
    split;[intros (f&_&h);exists f;assumption|].
    intros (ϕ&hϕ).
    destruct (list_of_functions_spec ϕ) as (ψ&Iψ&hψ).
    exists ψ;split;[assumption|].
    rewrite <- hψ;assumption.
  Qed.

  Global Instance dec_equiv_Pomsets : DecidableProp (P ≃ Q).
  Proof.
    cut (DecidableProp
           (exists ϕ, ϕ ∈ (list_of_functions (PomType Q) (PomType P)) /\ isomorphism ϕ));
      [|typeclasses eauto].
    intro D;eapply DecidableProp_equiv_prop;[apply D|clear D].
    split;[intros (f&_&h);exists f;assumption|].
    intros (ϕ&hϕ).
    destruct (list_of_functions_spec ϕ) as (ψ&Iψ&hψ).
    exists ψ;split;[assumption|].
    rewrite <- hψ;assumption.
  Qed.
  
  
End d.