Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import tools algebra.

Section s.
  Context {A : Type}.

  Notation Rel := (relation A).

  (** We define semantic (in)equality for binary relations in the usual way. *)
  Global Instance eqRel {A} : SemEquiv (relation A) :=
    (fun r s => forall x y, r x y <-> s x y).

  Global Instance infRel {A} : SemSmaller (relation A) :=
    (fun r s => forall x y, r x y -> s x y).

  (** Semantic equality is an equivalence relation, inequality is a partial order. *)
  Global Instance eqRel_Equivalence : Equivalence (@sequiv Rel (@eqRel A)).
  Proof.
    split;intro;unfold sequiv,eqRel;firstorder.
    - apply H0,H;auto.
    - apply H,H0;auto.
  Qed.

  Global Instance infRel_PreOrder : PreOrder (@ssmaller _ (@infRel A)).
  Proof. split;intro;unfold ssmaller,infRel;firstorder. Qed.

  Global Instance infRel_PartialOrder : PartialOrder sequiv (@ssmaller _ (@infRel A)).
  Proof. split;intro;unfold ssmaller,infRel;firstorder. Qed.

  Global Instance join_Rel : Join Rel :=
    fun x y a b => x a b \/ y a b.
 
  (** The product of two relations is their sequential composition. *)
  Global Instance prod_Rel : Product Rel :=
    fun r s x y =>  exists z, r x z /\ s z y.

  (** [𝟭] is the identity relation, also called diagonal. *)
   Global Instance unit_Rel : Un Rel := fun x y => x = y.

  (** [𝟬] is the empty relation. *)
   Global Instance zero_Rel : Zero Rel := fun _ _ => False.

   Reserved Notation " R ** n " (at level 40).
   
   Fixpoint power (R : Rel) n : Rel :=
     match n with
     | 0 => 𝟭
     | S n => R ⋅ (R ** n )
     end
   where " R ** n  " := (power R n).
   
   Global Instance star_Rel : Star Rel := fun R x y => exists n, (R ** n) x y.


   (** Congruence w.r.t. [≲]. *)
   Global Instance product_infRel : Proper (ssmaller==>ssmaller==>ssmaller) prod.
   Proof. intros r r' Er s s' Es x y;intros (z&R1&R2);exists z;split;apply Er||apply Es;auto. Qed.
   
   Global Instance plus_infRel : Proper (ssmaller==>ssmaller==>ssmaller) join.
   Proof.
     intros r r' Er s s' Es x y;intros [R|R];[left;apply Er|right;apply Es];assumption.
   Qed.
   
   Global Instance power_infRel : Proper (ssmaller==>Logic.eq==>ssmaller) power.
   Proof.
     intros r r' Er n ? <- ;induction n.
     - reflexivity.
     - intros x y (z&h1&h2);exists z;split.
       + apply Er,h1.
       + apply IHn,h2.
   Qed.
   
   Global Instance star_infRel : Proper (ssmaller==>ssmaller) star.
   Proof. intros r r' Er x y;intros (n&R);exists n;eapply power_infRel;eauto. Qed.
   
   (** Congruence w.r.t. [≃]. *)
   Global Instance product_eqRel : Proper (sequiv==>sequiv==>sequiv) prod.
   Proof.
     intros r r' Er s s' Es;apply antisymmetry;apply product_infRel;
       rewrite Er||rewrite Es;reflexivity.
   Qed.
   
   Global Instance plus_eqRel : Proper (sequiv==>sequiv==>sequiv) join.
   Proof.
     intros r r' Er s s' Es;apply antisymmetry;apply plus_infRel;
       rewrite Er||rewrite Es;reflexivity.
   Qed.
   
   Global Instance power_eqRel : Proper (sequiv==>Logic.eq==>sequiv) power.
   Proof.
     intros r r' Er s s' Es;apply antisymmetry;apply power_infRel;
       rewrite Er||rewrite Es;reflexivity.
   Qed.
   
   Global Instance star_eqRel : Proper (sequiv==>sequiv) star.
   Proof. intros r r' Er;apply antisymmetry;apply star_infRel;rewrite Er;reflexivity. Qed.
   
   (** Algebraic properties *)
   Global Instance RelationSemiRing : SemiRing Rel sequiv prod join un zero.
   Proof.
     split.
     - split.
       + apply product_eqRel.
       + intros r s t x y;split.
         * intros (z1&hr&z2&hs&ht);exists z2;split;[exists z1;split|];assumption.
         * intros (z2&(z1&hr&hs)&ht);exists z1;split;[|exists z2;split];assumption.
       + split.
         * intros r x y;split;[intros (z&->&h);assumption
                              |exists x;split;[reflexivity|assumption]].
         * intros r x y;split;[intros (z&h&->);assumption
                              |intro h;exists y;split;[assumption|reflexivity]].
     - split.
       + apply plus_eqRel.
       + intros r s t x y;split;intro h;repeat destruct h as [h|h];
           unfold join,join_Rel;tauto.
       + split;intros r x y;unfold join,zero,join_Rel,zero_Rel;tauto.
     - intros r s x y;unfold join,join_Rel;tauto.
     - split.
       + intros r x y;split;[intros (z&F&_);exfalso;apply F|intro F;exfalso;apply F].
       + intros r x y;split;[intros (z&_&F);exfalso;apply F|intro F;exfalso;apply F].
     - intros a b c x y;split.
       + intros (z&ha&[hb|hc]);[left|right];exists z;split;assumption.
       + intros [h|h];destruct h as (z&h1&h2);exists z;split;[|left| |right];assumption.
     - intros a b c x y;split.
       + intros (z&[ha|hb]&hc);[left|right];exists z;split;assumption.
       + intros [h|h];destruct h as (z&h1&h2);exists z;split;[left| |right|];assumption.
   Qed.

   Lemma leqA_ssmaller : leqA sequiv ≃ ssmaller.
   Proof.
     intros x y;unfold leqA,join,join_Rel,sequiv,ssmaller,eqRel,infRel;firstorder.
   Qed.

   Lemma power_Rel_last a n : a ** (S n) ≃ a ** n ⋅ a.
   Proof.
     induction n;simpl.
     - rewrite left_unit,right_unit;reflexivity.
     - rewrite IHn,(mon_assoc _),IHn;reflexivity.
   Qed.
   
   Global Instance RelationKleeneAlgebra : KleeneAlgebra Rel sequiv.
   Proof.
     split.
     - apply star_eqRel.
     - apply RelationSemiRing.
     - intros r x y;unfold join,join_Rel;tauto.
     - intros r;apply leqA_ssmaller.
       intros x y [->|(z&h1&n&h2)].
       + exists 0;reflexivity.
       + exists (S n),z;split;assumption.
     - intros a b E;apply leqA_ssmaller;apply leqA_ssmaller in E.
       intros x y (z&(n&ha)&hb).
       revert x y z ha hb;induction n;intros.
       + rewrite ha in *;assumption.
       + destruct ha as (t&ha&ih).
         apply E;exists t;split;[assumption|].
         apply (IHn t y z);assumption.
     - intros a b E;apply leqA_ssmaller;apply leqA_ssmaller in E.
       intros x y (z&ha&(n&hb)).
       revert x y z ha hb;induction n;intros.
       + rewrite hb in *;assumption.
       + apply power_Rel_last in hb as (t&ih&hb).
         apply E;exists t;split;[|assumption].
         apply (IHn x t z);assumption.
   Qed.

   Global Instance join_subrel_left R S : subrelation R (R∪S).
   Proof. apply leqA_ssmaller,inf_cup_left. Qed.
   
   Global Instance join_subrel_right R S : subrelation S (R∪S).
   Proof. apply leqA_ssmaller,inf_cup_right. Qed.


  (** Let [X] be a set. *)
  Context {X : Set}.
  (** Any map [σ : X -> relation A] may be uniquely extended into a monoid homomorphism [mapRel σ] from [list X] to [relation A]. *)
  Definition mapRel (σ : X -> relation A) (u : list X) :=
    fold_right (fun l r => σ l ⋅ r) 𝟭 u.

  Lemma mapRel_nil σ : mapRel σ [] = 𝟭.
  Proof. reflexivity. Qed.
  
  Lemma mapRel_app σ (u v : list X) : mapRel σ (u++v) ≃ mapRel σ u ⋅ mapRel σ v.
  Proof.
    induction u;simpl.
    - symmetry;apply left_unit.
    - rewrite IHu;apply mon_assoc.
  Qed.

  Lemma mapRel_unique σ h :
    (forall a, h [a] ≃ σ a) -> (h [] ≃ 𝟭) -> (forall u v, h (u++v) = h u ⋅ h v) ->
    forall u, h u ≃ mapRel σ u.
  Proof.
    intros ha hnil happ;induction u.
    - rewrite hnil;reflexivity.
    - simpl;rewrite <- IHu,<- ha,<-happ;simpl;reflexivity.
  Qed.
  
  Remark mapRel_add σ u a : mapRel σ (u++[a]) ≃ mapRel σ u ⋅ σ a.
  Proof. rewrite mapRel_app;simpl;rewrite right_unit;reflexivity. Qed.
  
End s.


  