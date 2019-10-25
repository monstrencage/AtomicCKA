Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools algebra Bool relations sp_terms pomsets.
Section s.
  Context {X : Set}.  
    
  Global Instance sem_sp : Semantics (sp_terms X) (Pomset X) :=
    fix I s :=
      match s with
      | sp_seq s1 s2 => I s1 ⋅ I s2
      | sp_par s1 s2 => I s1 ∥ I s2
      | sp_unit => 𝟭
      | sp_var x => AtomicPomset x
      end.

  Remark interpret_sp_seq s1 s2 : ⟦s1⋅s2⟧ =  ⟦s1⟧⋅⟦s2⟧.
  Proof. reflexivity. Qed.
  Remark interpret_sp_par s1 s2 : ⟦s1∥s2⟧ =  ⟦s1⟧∥⟦s2⟧.
  Proof. reflexivity. Qed.
  Remark interpret_sp_unit : ⟦𝟭⟧ = 𝟭.
  Proof. reflexivity. Qed.
  Hint Rewrite interpret_sp_unit interpret_sp_seq interpret_sp_par : simpl_typeclasses.

  Lemma soundness_sp_terms s t : s ≡ t -> ⟦s⟧ ≃ ⟦t⟧.
  Proof.
    intros E;induction E;rsimpl.
    - reflexivity.
    - symmetry;assumption.
    - etransitivity;eassumption.
    - rewrite IHE,IHE0;reflexivity.
    - rewrite IHE,IHE0;reflexivity.
    - apply mon_assoc.
    - apply mon_assoc.
    - apply bimon_comm.
    - apply left_unit.
    - apply right_unit.
    - apply left_unit.
  Qed.

  Lemma interpret_sp_size s : ⎢s⎥ = ⎢⟦s⟧⎥.
  Proof.
    induction s;rsimpl.
    - rewrite IHs1,IHs2.
      destruct ⟦s1⟧,⟦s2⟧;unfold size,sizePomset;simpl.
      rewrite size_node;reflexivity.
    - rewrite IHs1,IHs2.
      destruct ⟦s1⟧,⟦s2⟧;unfold size,sizePomset;simpl.
      rewrite size_node;reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.
  
  Theorem completeness_sp_terms s t : ⟦s⟧ ≃ ⟦t⟧ -> s ≡ t.
  Admitted.
End s.
      
Hint Rewrite @interpret_sp_unit @interpret_sp_seq @interpret_sp_par : simpl_typeclasses.
