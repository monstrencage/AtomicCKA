(** * RIS.algebra : algebraic structures. *)
(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)

Require Import tools.

(** * Definitions *)
Section algebra.
  (** Let [A] be some type equipped with an equivalence relation [⩵] and a partial order [≦]. *)
  Context {A : Type} {eqA: relation A}.
  Context {equivA : @Equivalence A eqA}.

  Infix " ⩵ " := eqA (at level 80).

  (** We introduce some notations. *)
  Class Un := un : A.
  Notation " 𝟭 " := un.

  Class Zero := zero : A.
  Notation " 𝟬 " := zero.
  
  Class Product := prod : A -> A -> A.
  Infix " ⋅ " := prod (at level 40).

  Class ParProduct := par : A -> A -> A.
  Infix " ∥ " := par (at level 42).

  Class Join := join : A -> A -> A.
  Infix " ∪ " := join (at level 45).

  Class Star := star : A -> A.
  Notation " e ⋆ " := (star e) (at level 35).

  (** ** Basic properties *)
  Class Associative (prod : A -> A -> A) :=
    associative : (forall a b c : A, prod a (prod b c) ⩵ prod (prod a b) c).
  Class Commutative (prod : A -> A -> A) :=
    commutative : (forall a b : A, prod a b ⩵ prod b a).
  Class Idempotent (prod : A -> A -> A) :=
    idempotent : (forall a : A, prod a a ⩵ a).
  Class Unit (prod : A -> A -> A) (unit : A) :=
    {
      left_unit : forall a : A, prod unit a ⩵ a;
      right_unit : forall a : A, prod a unit ⩵ a
    }.
  Class Absorbing (prod : A -> A -> A) (z : A) :=
    {
      left_absorbing : forall a : A, prod z a ⩵ z;
      right_absorbing : forall a : A, prod a z ⩵ z
    }.

  (** ** Basic structures *)
  Class Monoid (prod : A -> A -> A) (unit : A) :=
    {
      mon_congr :> Proper (eqA ==> eqA ==> eqA) prod;
      mon_assoc :> Associative prod;
      mon_unit :> Unit prod unit;
    }.

  Class BiMonoid (prod : A -> A -> A) (par : A -> A -> A) (unit : A) :=
    {
      bimon_seq :> Monoid prod unit;
      bimon_par :> Monoid par unit;
      bimon_comm :> Commutative par
    }.
  
  Class Semilattice (join : A -> A -> A) :=
    {
      lat_congr :> Proper (eqA ==> eqA ==> eqA) join;
      lat_assoc :> Associative join;
      lat_comm :> Commutative join;
      lat_idem :> Idempotent join;
    }.
  
  Class Lattice (m j : A -> A -> A) :=
    {
      lat_meet_congr :> Proper (eqA ==> eqA ==> eqA) m;
      lat_meet_assoc :> Associative m;
      lat_meet_comm :> Commutative m;
      lat_join_congr :> Proper (eqA ==> eqA ==> eqA) j;
      lat_join_assoc :> Associative j;
      lat_join_comm :> Commutative j;
      lat_join_meet : forall a b, j a (m a b) ⩵ a;
      lat_meet_join : forall a b, m a (j a b) ⩵ a;
    }.

  Class SemiRing (prod add : A -> A -> A) (u z : A) :=
    {
      semiring_prod :> Monoid prod u;
      semiring_add :> Monoid add z;
      semiring_comm :> Commutative add;
      semiring_zero :> Absorbing prod z;
      semiring_left_distr : forall a b c, prod a (add b c) ⩵ add (prod a b) (prod a c);
      semiring_right_distr : forall a b c, prod (add a b) c ⩵ add (prod a c) (prod b c);
    }.

  Class BiSemiRing (prod par add : A -> A -> A) (u z : A) :=
    {
      bisemiring_bimon :> BiMonoid prod par u;
      bisemiring_add :> Monoid add z;
      bisemiring_comm :> Commutative add;
      bisemiring_zero_seq :> Absorbing prod z;
      bisemiring_zero_par :> Absorbing par z;
      bisemiring_left_distr : forall a b c, prod a (add b c) ⩵ add (prod a b) (prod a c);
      bisemiring_right_distr : forall a b c, prod (add a b) c ⩵ add (prod a c) (prod b c);
      bisemiring_par_distr : forall a b c, par a (add b c) ⩵ add (par a b) (par a c);
    }.

  (** ** Join semi-lattices *)
  Section order.
    Context {j : Join}.
    Context {S : Semilattice join}.
    
    Definition leqA : relation A := (fun x y => y ⩵ x ∪ y).
    Infix " ≦ " := leqA (at level 80).

    Global Instance preA : PreOrder leqA.
    Proof.
      destruct S as [p ass comm id];unfold leqA.
      split.
      - intro x;symmetry;apply id.
      - intros x y z e1 e2.
        rewrite e2 at 2.
        rewrite (ass x y z),<- e1.
        apply e2.
    Qed.

    Global Instance partialA : PartialOrder eqA leqA.
    Proof.
      destruct S as [p ass comm id].
      intros x y;unfold Basics.flip,leqA;split.
      - intros E;split.
        + rewrite E,(id y);reflexivity.
        + rewrite E;symmetry;apply id.
      - intros (E1&E2).
        rewrite E1.
        rewrite E2 at 1.
        apply comm.
    Qed.
    
    Lemma refactor e f g h : (e ∪ f) ∪ (g ∪ h) ⩵ (e ∪ g) ∪ (f ∪ h).
    Proof.
      rewrite (lat_assoc (e∪f) g h).
      rewrite <- (lat_assoc e f g).
      rewrite (@lat_comm _ S f g).
      rewrite (lat_assoc e g f).
      rewrite (lat_assoc (e∪g) f h).
      reflexivity.
    Qed.

    Global Instance proper_join_inf : Proper (leqA ==> leqA ==> leqA) join.
    Proof.
      intros x y I x' y' I';unfold leqA in *.
      rewrite I,I' at 1;apply refactor.
    Qed.

    Lemma inf_cup_left a b : a ≦ a ∪ b.
    Proof. unfold leqA; rewrite (lat_assoc _ _ _),(lat_idem _);reflexivity. Qed.

    Lemma inf_cup_right a b : b ≦ a ∪ b.
    Proof. rewrite (lat_comm a b);apply inf_cup_left. Qed.

    Lemma inf_join_inf a b c : a ≦ c -> b ≦ c -> a ∪ b ≦ c.
    Proof. intros;rewrite <- (lat_idem c); apply proper_join_inf;assumption. Qed.

    Context {z : Zero} {u : Unit join zero}.
  
    Lemma zero_minimal x : zero ≦ x.
    Proof. unfold leqA;symmetry ;apply left_unit. Qed.

  End order.
      
  Infix " ≦ " := leqA (at level 80).


  (** ** Kleene algebra and Boolean algebra *)
  Class KleeneAlgebra (j: Join) (p: Product) (z: Zero) (u:Un) (s:Star) :=
    {
      ka_star_congr :> Proper (eqA ==> eqA) star;
      ka_semiring :> SemiRing prod join un zero;
      ka_idem :> Idempotent join;
      ka_star_unfold : forall a, 𝟭 ∪ a ⋅ a ⋆ ≦ a⋆ ;
      ka_star_left_ind : forall a b, a ⋅ b ≦ b -> a ⋆ ⋅ b ≦ b;
      ka_star_right_ind : forall a b, a ⋅ b ≦ a -> a ⋅ b ⋆ ≦ a;
    }.

  Class BiKleeneAlgebra
        (j: Join) (seq: Product) (par : ParProduct) (z: Zero) (u:Un) (s:Star) :=
    {
      bika_star_congr :> Proper (eqA ==> eqA) star;
      bika_semiring :> BiSemiRing prod par join un zero;
      bika_idem :> Idempotent join;
      bika_star_unfold : forall a, 𝟭 ∪ a ⋅ a ⋆ ≦ a⋆ ;
      bika_star_left_ind : forall a b, a ⋅ b ≦ b -> a ⋆ ⋅ b ≦ b;
      bika_star_right_ind : forall a b, a ⋅ b ≦ a -> a ⋅ b ⋆ ≦ a;
    }.

  Class BooleanAlgebra (t f : A) (n : A -> A) (c d: A -> A -> A) :=
    {
      proper_c :> Proper (eqA ==> eqA ==> eqA) c;
      proper_d :> Proper (eqA ==> eqA ==> eqA) d;
      proper_n :> Proper (eqA ==> eqA) n;
      ba_conj_comm :> Commutative c;
      ba_disj_comm :> Commutative d;
      ba_true : forall a, c a t ⩵ a;
      ba_false : forall a, d a f ⩵ a;
      ba_conj_disj : forall x y z, c x (d y z) ⩵ d (c x y) (c x z);
      ba_disj_conj : forall x y z, d x (c y z) ⩵ c (d x y) (d x z);
      ba_neg_conj : forall a, c a (n a) ⩵ f;
      ba_neg_disj : forall a, d a (n a) ⩵ t;
    }.
  
End algebra.
Arguments Zero: clear implicits.
Arguments Un: clear implicits.
Arguments Product: clear implicits.
Arguments ParProduct: clear implicits.
Arguments Join: clear implicits.
Arguments Star: clear implicits.
Notation " 𝟭 " := un.
Notation " 𝟬 " := zero.
Infix " ⋅ " := prod (at level 40).
Infix " ∥ " := par (at level 42).
Infix " ∪ " := join (at level 45).
Notation " e ⋆ " := (star e) (at level 35).

Class Box A := box : A -> A.
Notation " ▢ " := box.

Arguments Monoid : clear implicits.
Arguments BiMonoid : clear implicits.
Arguments KleeneAlgebra : clear implicits.
Arguments KleeneAlgebra A eqA {j p z u s}.
Arguments SemiRing : clear implicits.
Arguments BiKleeneAlgebra : clear implicits.
Arguments BiKleeneAlgebra A eqA {j seq par z u s}.
Arguments BiSemiRing : clear implicits.
Arguments Semilattice : clear implicits.
Arguments BooleanAlgebra : clear implicits.
Arguments BooleanAlgebra {A} eqA t f n c d.
Arguments leqA : clear implicits.
Arguments leqA {A} eqA {j}.

(** * Facts about boolean algebra *)
Section booleanAlgebra.
  Context {A : Type} {eqA: relation A}.
  Context {equivA : @Equivalence A eqA}.

  Infix " ⩵ " := eqA (at level 80).
  Context {top bot : A} {neg : A -> A} {conj disj : A -> A -> A}.
  Context `{BooleanAlgebra A eqA top bot neg conj disj}.

  Notation " ⊤ " := top.
  Notation " ⊥ " := bot.
  Notation " ¬ " := neg.
  Infix " ∧ " := conj (at level 40).
  Infix " ∨ " := disj (at level 45).

  (** When we defined boolean algebra before, we relied on
  Huntington's 1904 axiomatization, which differs from the usual way
  they are defined, but is much more concise. We now show that this
  axiomatization indeed implies all the properties we expect of a
  boolean algebra. The following subsection is a straightforward
  adaptation of the proofs detailed on the wikipedia page of boolean
  algebra: 
  #<a href="https://en.wikipedia.org/wiki/Boolean_algebra_(structure)##Axiomatics">en.wikipedia.org/wiki/Boolean_algebra_(structure)</a>#.*)

  (** ** Elementary properties *)
  Lemma UId1 o : (forall x, x ∨ o ⩵ x) -> o ⩵ ⊥.
  Proof.
    intros hyp.
    rewrite <- (ba_false o).
    rewrite (ba_disj_comm _ _).
    apply hyp.
  Qed.
  
  Lemma Idm1 x : x ∨ x ⩵ x.
  Proof.
    rewrite <- (ba_true (x∨x)),<-(ba_neg_disj x).
    rewrite <- ba_disj_conj,ba_neg_conj.
    apply ba_false.
  Qed.

  Lemma Bnd1 x : x ∨ ⊤ ⩵ ⊤.
  Proof.
    rewrite <- (ba_true (x∨⊤)),(ba_conj_comm _ _).
    rewrite <- (ba_neg_disj x) at 1.
    rewrite <- ba_disj_conj,ba_true.
    apply ba_neg_disj.
  Qed.

  Lemma Abs1 x y : x ∨ (x ∧ y) ⩵ x.
  Proof.
    rewrite <- (ba_true x) at 1.
    rewrite <- ba_conj_disj,(ba_disj_comm _ _),Bnd1.
    apply ba_true.
  Qed.

  Lemma UId2 o : (forall x, x ∧ o ⩵ x) -> o ⩵ ⊤.
  Proof.
    intros hyp.
    rewrite <- (ba_true o).
    rewrite (ba_conj_comm _ _).
    apply hyp.
  Qed.
  
  Lemma Idm2 x : x ∧ x ⩵ x.
  Proof.
    rewrite <- (ba_false (x∧x)),<-(ba_neg_conj x).
    rewrite <- ba_conj_disj,ba_neg_disj.
    apply ba_true.
  Qed.

  Lemma Bnd2 x : x ∧ ⊥ ⩵ ⊥.
  Proof.
    rewrite <- (ba_false (x∧⊥)),(ba_disj_comm _ _).
    rewrite <- (ba_neg_conj x) at 1.
    rewrite <- ba_conj_disj,ba_false.
    apply ba_neg_conj.
  Qed.

  Lemma Abs2 x y : x ∧ (x ∨ y) ⩵ x.
  Proof.
    rewrite <- (ba_false x) at 1.
    rewrite <- ba_disj_conj,(ba_conj_comm _ _),Bnd2.
    apply ba_false.
  Qed.
  
  Lemma UNg x x' : x ∨ x' ⩵ ⊤ -> x ∧ x' ⩵ ⊥ -> x' ⩵ ¬ x.
  Proof.
    intros h1 h2.
    rewrite <- (ba_true x'),<-(ba_neg_disj x),ba_conj_disj,(ba_conj_comm x' _),(ba_conj_comm x' _).
    rewrite h2.
    rewrite <- (ba_neg_conj x),(ba_conj_comm _ _),<-ba_conj_disj.
    rewrite h1.
    apply ba_true.
  Qed.

  Lemma DNg x : ¬(¬ x) ⩵ x.
  Proof.
    symmetry;apply UNg.
    - rewrite (ba_disj_comm _ _);apply ba_neg_disj.
    - rewrite (ba_conj_comm _ _);apply ba_neg_conj.
  Qed.

  Lemma A1 x y : x ∨ (¬ x ∨ y) ⩵ ⊤.
  Proof.
    rewrite <- (ba_true (x∨_)),(ba_conj_comm _ _),<-(ba_neg_disj x).
    rewrite <- ba_disj_conj.
    rewrite Abs2;reflexivity.
  Qed.

  Lemma A2 x y : x ∧ (¬ x ∧ y) ⩵ ⊥.
  Proof.
    rewrite <- (ba_false (x∧_)),(ba_disj_comm _ _),<-(ba_neg_conj x).
    rewrite <- ba_conj_disj.
    rewrite Abs1;reflexivity.
  Qed.

  Lemma B1 x y : (x ∨ y)∨(¬x∧¬y)⩵⊤.
  Proof.
    rewrite ba_disj_conj.
    rewrite (ba_disj_comm _ (¬x)), (ba_disj_comm _ (¬y)).
    rewrite (ba_disj_comm x y) at 2.
    rewrite <- (DNg x) at 2.
    rewrite <- (DNg y) at 3.
    repeat rewrite A1.
    apply ba_true.
  Qed.
    
  Lemma B2 x y : (x ∧ y)∧(¬x∨¬y)⩵⊥.
  Proof.
    rewrite ba_conj_disj.
    rewrite (ba_conj_comm _ (¬x)), (ba_conj_comm _ (¬y)).
    rewrite (ba_conj_comm x y) at 2.
    rewrite <- (DNg x) at 2.
    rewrite <- (DNg y) at 3.
    repeat rewrite A2.
    apply ba_false.
  Qed.

  Lemma C1 x y : (x ∨ y)∧ (¬x∧¬y)⩵⊥.
  Proof.
    rewrite (ba_conj_comm (x∨_) _),ba_conj_disj.
    rewrite (ba_conj_comm _ x),(ba_conj_comm _ y).
    rewrite (ba_conj_comm _ (¬y)) at 2.
    repeat rewrite A2.
    apply ba_false.
  Qed.

  Lemma C2 x y : (x ∧ y)∨ (¬x∨¬y)⩵⊤.
  Proof.
    rewrite (ba_disj_comm (x∧_) _),ba_disj_conj.
    rewrite (ba_disj_comm _ x),(ba_disj_comm _ y).
    rewrite (ba_disj_comm _ (¬y)) at 2.
    repeat rewrite A1.
    apply ba_true.
  Qed.

  Lemma DMg1 x y : ¬ (x∨y) ⩵ ¬ x ∧ ¬ y.
  Proof.
    symmetry;apply UNg.
    - apply B1.
    - apply C1.
  Qed.

  Lemma DMg2 x y : ¬ (x∧y) ⩵ ¬ x ∨ ¬ y.
  Proof.
    symmetry;apply UNg.
    - apply C2.
    - apply B2.
  Qed.

  Lemma D1 x y z : (x∨(y∨z))∨¬x⩵⊤.
  Proof.
    rewrite (ba_disj_comm _ (¬x)).
    rewrite <- (DNg x) at 2.
    apply A1.
  Qed.

  Lemma D2 x y z : (x∧(y∧z))∧¬x⩵⊥.
  Proof.
    rewrite (ba_conj_comm _ (¬x)).
    rewrite <- (DNg x) at 2.
    apply A2.
  Qed.

  Lemma E1 x y z : y∧(x∨(y∨z))⩵ y.
  Proof.
    rewrite ba_conj_disj,Abs2,(ba_disj_comm _).
    apply Abs1.
  Qed.

  Lemma E2 x y z : y∨(x∧(y∧z))⩵ y.
  Proof.
    rewrite ba_disj_conj,Abs1,(ba_conj_comm _).
    apply Abs2.
  Qed.

  Lemma F1 x y z : (x∨(y∨z))∨¬y ⩵ ⊤.
  Proof.
    rewrite (ba_disj_comm _ (¬ _)).
    rewrite <- ba_true,(ba_conj_comm _ _),<-(ba_neg_disj y) at 1.
    rewrite (ba_disj_comm y),<-ba_disj_conj,E1,(ba_disj_comm _ y).
    apply ba_neg_disj.
  Qed.

  Lemma F2 x y z : (x∧(y∧z))∧¬y ⩵ ⊥.
  Proof.
    rewrite (ba_conj_comm _ (¬ _)).
    rewrite <- ba_false,(ba_disj_comm _ _),<-(ba_neg_conj y) at 1.
    rewrite (ba_conj_comm y),<-ba_conj_disj,E2,(ba_conj_comm _ y).
    apply ba_neg_conj.
  Qed.

  Lemma G1 x y z : (x ∨(y∨z))∨¬z⩵⊤.
  Proof. rewrite (ba_disj_comm y z);apply F1. Qed.

  Lemma G2 x y z : (x ∧(y∧z))∧¬z⩵⊥.
  Proof. rewrite (ba_conj_comm y z);apply F2. Qed.

  Lemma H1 x y z : ¬ ((x∨y)∨z)∧x⩵⊥.
  Proof.
    rewrite DMg1,DMg1.
    rewrite (ba_conj_comm _).
    rewrite <- ba_false,(ba_disj_comm _).
    rewrite <- (ba_neg_conj x) at 1.
    rewrite <- ba_conj_disj,(ba_conj_comm _ (¬z)),E2.
    apply ba_neg_conj.
  Qed.

  Lemma H2 x y z : ¬ ((x∧y)∧z)∨x⩵⊤.
  Proof.
    rewrite DMg2,DMg2.
    rewrite (ba_disj_comm _).
    rewrite <- ba_true,(ba_conj_comm _).
    rewrite <- (ba_neg_disj x) at 1.
    rewrite <- ba_disj_conj,(ba_disj_comm _ (¬z)),E1.
    apply ba_neg_disj.
  Qed.

  Lemma I1 x y z : ¬ ((x∨y)∨z)∧y⩵⊥.
  Proof. rewrite (ba_disj_comm x y);apply H1. Qed.

  Lemma I2 x y z : ¬ ((x∧y)∧z)∨y⩵⊤.
  Proof. rewrite (ba_conj_comm x y);apply H2. Qed.

  Lemma J1 x y z : ¬((x∨y)∨z)∧z⩵⊥.
  Proof. rewrite DMg1,(ba_conj_comm _),(ba_conj_comm (¬ _));apply A2. Qed.

  Lemma J2 x y z : ¬((x∧y)∧z)∨z⩵⊤.
  Proof. rewrite DMg2,(ba_disj_comm _),(ba_disj_comm (¬ _));apply A1. Qed.

  Lemma K1 x y z : (x∨(y∨z))∨¬((x∨y)∨z)⩵⊤.
  Proof.
    repeat rewrite DMg1.
    repeat rewrite ba_disj_conj.
    rewrite D1,F1,G1.
    repeat rewrite ba_true;reflexivity.
  Qed.
  
  Lemma K2 x y z : (x∧(y∧z))∧¬((x∧y)∧z)⩵⊥.
  Proof.
    repeat rewrite DMg2.
    repeat rewrite ba_conj_disj.
    rewrite D2,F2,G2.
    repeat rewrite ba_false;reflexivity.
  Qed.
  
  Lemma L1 x y z : (x∨(y∨z))∧¬((x∨y)∨z) ⩵ ⊥.
  Proof.
    rewrite (ba_conj_comm _).
    repeat rewrite ba_conj_disj.
    rewrite H1,I1,J1.
    repeat rewrite ba_false;reflexivity.
  Qed.
  
  Lemma L2 x y z : (x∧(y∧z))∨¬((x∧y)∧z) ⩵ ⊤.
  Proof.
    rewrite (ba_disj_comm _).
    repeat rewrite ba_disj_conj.
    rewrite H2,I2,J2.
    repeat rewrite ba_true;reflexivity.
  Qed.

  Lemma Ass1 x y z : x∨(y∨z)⩵(x∨y)∨z.
  Proof.
    rewrite <- (DNg ((x∨y)∨z));apply UNg.
    - rewrite (ba_disj_comm _);apply K1.
    - rewrite (ba_conj_comm _);apply L1.
  Qed.

  Lemma Ass2 x y z : x∧(y∧z)⩵(x∧y)∧z.
  Proof.
    rewrite <- (DNg ((x∧y)∧z));apply UNg.
    - rewrite (ba_disj_comm _);apply L2.
    - rewrite (ba_conj_comm _);apply K2.
  Qed.

  (** ** Boolean algebra as other structures*)
  Global Instance BooleanAlgebra_Join_Lattice : @Lattice A eqA conj disj.
  Proof.
    split.
    - apply H.
    - intros x y z;apply Ass2.
    - apply ba_conj_comm.
    - apply H.
    - intros x y z;apply Ass1.
    - apply ba_disj_comm.
    - apply Abs1.
    - apply Abs2.
  Qed.
  
  Global Instance BooleanAlgebra_Join_Semilattice : Semilattice A eqA disj.
  Proof.
    split.
    - apply H.
    - apply lat_join_assoc.
    - apply lat_join_comm.
    - intros a;apply Idm1.
  Qed.

  Global Instance BooleanAlgebra_Meet_Semilattice : Semilattice A eqA conj.
  Proof.
    split.
    - apply H.
    - apply lat_meet_assoc.
    - apply lat_meet_comm.
    - intros a;apply Idm2.
  Qed.

  Global Instance BooleanAlgebra_Meet_Monoid : @Monoid A eqA conj top.
  Proof.
    split.
    - apply H.
    - apply lat_meet_assoc.
    - split.
      + intro a;etransitivity;[apply lat_meet_comm|apply ba_true].
      + apply ba_true.
  Qed.

  Global Instance BooleanAlgebra_Join_Monoid : @Monoid A eqA disj bot.
  Proof.
    split.
    - apply H.
    - apply lat_join_assoc.
    - split.
      + intro a;etransitivity;[apply lat_join_comm|apply ba_false].
      + apply ba_false.
  Qed.

  Global Instance BooleanAlgebra_Semiring : SemiRing A eqA conj disj top bot.
  Proof.
    split.
    - eapply BooleanAlgebra_Meet_Monoid;eassumption.
    - eapply BooleanAlgebra_Join_Monoid;eassumption.
    - apply lat_join_comm.
    - split.
      + intros a;rewrite (ba_conj_comm _);apply Bnd2.
      + intros a;apply Bnd2.
    - apply ba_conj_disj.
    - intros x y z;rewrite (ba_conj_comm _),ba_conj_disj.
      repeat rewrite (ba_conj_comm z);reflexivity.
  Qed.

End booleanAlgebra.
(** * Sums *)
Section sums.
  Context {A : Type} {eqA: relation A}.
  Context {equivA : @Equivalence A eqA}.
  
  Infix " ⩵ " := eqA (at level 80).
  
  Context {j: Join A}{z: Zero A}.
  Context {j_mon : Monoid A eqA join zero}.
  Context {j_comm : @Commutative A eqA join}.
  Context {j_idem : @Idempotent A eqA join}.

  Infix " ≦ " := (leqA eqA) (at level 80).
  Instance semi_lat : Semilattice A eqA join.
  Proof.
    split;auto.
    - apply mon_congr.
    - apply mon_assoc.
  Qed.
  
  Definition Σ l := fold_right (fun e f => join e f) zero l.

  Lemma Σ_app L M : Σ L ∪ Σ M ⩵ Σ (L++M).
  Proof.
    induction L;simpl;[|rewrite <- IHL].
    - apply left_unit.
    - symmetry;apply mon_assoc.
  Qed.
      
  Lemma Σ_incl L M : L ⊆ M -> Σ L ≦ Σ M.
  Proof.
    intro I;unfold leqA;rewrite Σ_app;revert M I;induction L;intros M I.
    - reflexivity.
    - simpl;rewrite <- IHL by (rewrite <- I;intro;simpl;tauto).
      assert (Ia : a ∈ M) by (apply I;now left).
      clear I L IHL.
      induction M as [|e L].
      + simpl in *;tauto.
      + simpl;destruct Ia as [->|Ia];simpl.
        * rewrite (mon_assoc _ _ _),(j_idem _);reflexivity.
        * rewrite IHL at 1 by assumption.
          rewrite (mon_assoc _ _ _),(j_comm e a),(mon_assoc _ _ _);reflexivity.
  Qed.  
  
  Global Instance Σ_equivalent : Proper (@equivalent _ ==> eqA) Σ.
  Proof.
    intros l1 l2 E.
    apply antisymmetry;apply Σ_incl;rewrite E;reflexivity.
  Qed.

  Lemma Σ_bigger e L : e ∈ L -> e ≦ Σ L.
  Proof.
     intro I;transitivity (Σ [e]).
     - simpl;apply inf_cup_left.
     - apply Σ_incl;intros ? [<-|F];simpl in *;tauto.
  Qed.
  
  Lemma Σ_bounded e L : (forall f, f ∈ L -> f ≦ e) <-> Σ L ≦ e.
  Proof.
    split.
    - induction L;simpl;intro I.
      + apply zero_minimal.
      + rewrite IHL by (intros ? ?;apply I;now right).
        rewrite (I a) by now left.
        rewrite (j_idem e);reflexivity.
    - intros E f If.
      rewrite <- E;apply Σ_bigger,If.
  Qed.
End sums.

(** * Products *)
Section prods.
  Context {A : Type} {eqA: relation A}.
  Context {equivA : @Equivalence A eqA}.
  
  Infix " ⩵ " := eqA (at level 80).
  
  Context {m : Product A}{u: Un A}.
  Context {j_mon : Monoid A eqA prod un}.

  Definition Π l := fold_right (fun e f => e ⋅ f) 𝟭 l.

  Lemma Π_app L M : Π L ⋅ Π M ⩵ Π (L++M).
  Proof.
    induction L;simpl;[|rewrite <- IHL].
    - apply left_unit.
    - symmetry;apply mon_assoc.
  Qed.

  Fixpoint Power (β : A) n :=
    match n with
    | 0 => 𝟭
    | S n => β ⋅ Power β n
    end.
  Infix " ^ " := Power.

  Global Instance Power_proper :
    Proper (eqA ==> eq ==> eqA) Power.
  Proof.
    intros a b E n _ <-;induction n;simpl.
    - reflexivity.
    - rewrite IHn,E;reflexivity.
  Qed.

  Lemma Power_last a n : a ^ (S n) ⩵ a ^ n ⋅ a.
  Proof.
    induction n;simpl.
    - rewrite left_unit,right_unit;reflexivity.
    - rewrite IHn,(mon_assoc _),IHn;reflexivity.
  Qed.

  Lemma Power_add a x y : a ^ (x + y) ⩵ a ^ x ⋅ a ^ y.
  Proof.
    induction x;simpl.
    - rewrite left_unit;reflexivity.
    - rewrite IHx;apply mon_assoc.
  Qed.
End prods.
Infix " ^ " := Power.

(** * Parallel Products *)
Section parprods.
  Context {A : Type} {eqA: relation A}.
  Context {equivA : @Equivalence A eqA}.
  
  Infix " ⩵ " := eqA (at level 80).
  
  Context {m : ParProduct A}{u: Un A}.
  Context {j_mon : Monoid A eqA par un}.

  Definition ParΠ l := fold_right (fun e f => e ∥ f) 𝟭 l.
  Notation " ! " := ParΠ.

  Lemma ParΠ_app L M : ! L ∥ ! M ⩵ ! (L++M).
  Proof.
    induction L;simpl;[|rewrite <- IHL].
    - apply left_unit.
    - symmetry;apply mon_assoc.
  Qed.
      
End parprods.
Notation " ! " := ParΠ.

Section idempotent_semirings.
  Context {A : Type} {eqA: relation A}.
  Context {equivA : @Equivalence A eqA}.
  
  Infix " ⩵ " := eqA (at level 80).
  
  Context {j: Join A}{p: Product A}{z: Zero A}{u:Un A}.
  Context {sr: SemiRing A eqA prod join un zero}.
  Context {idj: @Idempotent A eqA join}.

  Infix " ≦ " := (leqA eqA) (at level 80).
  
  Global Instance proper_prod_inf : Proper (leqA eqA ==> leqA eqA ==> leqA eqA) prod.
  Proof.
    intros e f I e' f' I'.
    unfold leqA in *.
    rewrite I' at 1.
    rewrite semiring_left_distr.
    rewrite I at 1.
    rewrite semiring_right_distr.
    rewrite <- (mon_assoc _ _ _).
    rewrite <- semiring_left_distr.
    rewrite <- I'.
    reflexivity.
  Qed.
  
  Instance join_semilattice : Semilattice A eqA join.
  Proof. split;apply sr||apply idj. Qed.
  
  Lemma Σ_distr_l e L : e ⋅ Σ L ⩵ Σ (map (prod e) L).
  Proof.
    induction L;simpl.
    - apply right_absorbing.
    - rewrite <- IHL,semiring_left_distr;reflexivity.
  Qed.
  
  Lemma Σ_distr_r e L : Σ L ⋅ e ⩵ Σ (map (fun f => f ⋅ e) L).
  Proof.
    induction L;simpl.
    - apply left_absorbing.
    - rewrite <- IHL,semiring_right_distr;reflexivity.
  Qed.

End idempotent_semirings.


(** * Kleene algebras *)
Section ka_facts.
  Context {A : Type} {eqA: relation A}.
  Context {equivA : @Equivalence A eqA}.
  
  Infix " ⩵ " := eqA (at level 80).
  
  Context {j: Join A}{p: Product A}{z: Zero A}{u:Un A}{s:Star A}.
  Context {ka: KleeneAlgebra A eqA}.

  Infix " ≦ " := (leqA eqA) (at level 80).

  Global Instance ka_join_semilattice : Semilattice A eqA join:= join_semilattice.
  
  Lemma ka_star_unfold_eq a : a⋆ ⩵ 𝟭 ∪ a ⋅ a ⋆.
  Proof.
    apply antisymmetry.
    - etransitivity;[|apply ka_star_left_ind with (a0:=a)].
      + rewrite (semiring_left_distr _ _ _). 
        rewrite right_unit. 
        apply inf_cup_left.
      + rewrite (semiring_left_distr _ _ _).
        rewrite right_unit.
        apply inf_join_inf.
        * rewrite <- inf_cup_right.
          rewrite <- ka_star_unfold.
          rewrite (semiring_left_distr _ _ _).
          rewrite <- inf_cup_left.
          rewrite right_unit.
          reflexivity.
        * rewrite <- ka_star_unfold at 2.
          rewrite <- inf_cup_right.
          rewrite (semiring_left_distr _ _ _).
          rewrite <- inf_cup_right.
          reflexivity.
    - apply ka_star_unfold.
  Qed.
  
  Lemma ka_star_dup a : a ⋆ ⋅ a ⋆ ⩵ a ⋆.
  Proof.
    apply antisymmetry.
    - apply ka_star_left_ind.
      rewrite ka_star_unfold_eq at 2.
      apply inf_cup_right.
    - rewrite ka_star_unfold_eq at 1.
      apply inf_join_inf.
      + rewrite ka_star_unfold_eq.
        rewrite (semiring_left_distr _ _ _).
        rewrite (semiring_right_distr _ _ _).
        rewrite <- inf_cup_left.
        rewrite <- inf_cup_left.
        rewrite left_unit.
        reflexivity.
      + apply proper_prod_inf;[|reflexivity].
        rewrite ka_star_unfold_eq.
        rewrite <- inf_cup_right.
        rewrite ka_star_unfold_eq.
        rewrite (semiring_left_distr _ _ _).
        rewrite <- inf_cup_left.
        rewrite right_unit.
        reflexivity.
  Qed.

  Lemma one_inf_star e : 𝟭 ≦ e⋆.
  Proof. rewrite ka_star_unfold_eq;apply inf_cup_left. Qed.

  Lemma star_incr e : e ≦ e⋆.
  Proof. rewrite ka_star_unfold_eq, <- one_inf_star,right_unit;apply inf_cup_right. Qed.
    
  Global Instance proper_star_inf : Proper (leqA eqA ==> leqA eqA) star.
  Proof.
    intros e f I.
    transitivity (e⋆⋅𝟭);[rewrite right_unit;reflexivity|].
    rewrite (one_inf_star f).
    apply ka_star_left_ind.
    rewrite I,(star_incr f),ka_star_dup at 1;reflexivity.
  Qed.
  
  Lemma ka_star_star a : a⋆ ⩵ (a ⋆)⋆.
  Proof.
    apply antisymmetry.
    - apply proper_star_inf.
      rewrite ka_star_unfold_eq.
      rewrite <- inf_cup_right.
      rewrite ka_star_unfold_eq.
      rewrite (semiring_left_distr _ _ _).
      rewrite right_unit.
      apply inf_cup_left.
    - rewrite ka_star_unfold_eq at 1.
      apply inf_join_inf.
      + rewrite ka_star_unfold_eq.
        apply inf_cup_left.
      + apply ka_star_right_ind.
        rewrite ka_star_dup.
        reflexivity.
  Qed.        
  
  Lemma ka_star_unfold_right a : 𝟭 ∪ a⋆ ⋅ a ≦ a⋆.
  Proof.
    apply inf_join_inf.
    - rewrite ka_star_unfold_eq.
      apply inf_cup_left.
    - rewrite <- ka_star_dup at 2.
      apply proper_prod_inf.
      + reflexivity.
      + rewrite ka_star_unfold_eq,ka_star_unfold_eq.
        rewrite semiring_left_distr,right_unit.
        rewrite <- inf_cup_right.
        apply inf_cup_left.
  Qed.

  Lemma star_join e f : (e ∪ f)⋆ ⩵ e ⋆ ∪ f⋆⋅(e⋅f⋆)⋆.
  Proof.
    apply antisymmetry.
    - transitivity ((e ∪ f) ⋆ ⋅ un);[rewrite right_unit;reflexivity|].
      transitivity ((e ∪ f) ⋆ ⋅ (e ⋆ ∪ f ⋆ ⋅ (e ⋅ f ⋆) ⋆)).
      + apply proper_prod_inf;[reflexivity|].
        etransitivity;[|apply inf_cup_left].
        apply one_inf_star.
      + apply ka_star_left_ind.
        rewrite semiring_left_distr.
        repeat rewrite semiring_right_distr.
        repeat apply inf_join_inf.
        * etransitivity;[|apply inf_cup_left].
          rewrite (star_incr e) at 1.
          rewrite ka_star_dup;reflexivity.
        * etransitivity;[|apply inf_cup_right].
          apply proper_prod_inf;[apply star_incr|].
          rewrite <- (one_inf_star f),right_unit;reflexivity.
        * etransitivity;[|apply inf_cup_right].
          rewrite <- (one_inf_star f) at 3;rewrite left_unit.
          rewrite <- (ka_star_dup (e⋅f⋆)) at 2.
          rewrite <- (star_incr (e⋅f⋆)) at 2.
          rewrite (mon_assoc _ _ _).
          reflexivity.
        * etransitivity;[|apply inf_cup_right].
          rewrite (mon_assoc _ _ _).
          apply proper_prod_inf;[|reflexivity].
          rewrite (star_incr f) at 1;rewrite ka_star_dup;reflexivity.
    - apply inf_join_inf.
      + apply proper_star_inf,inf_cup_left.
      + rewrite <- (ka_star_dup (e∪f)).
        apply proper_prod_inf;[apply proper_star_inf,inf_cup_right|].
        rewrite (ka_star_star (e∪f)).
        apply proper_star_inf.
        rewrite <- (ka_star_dup (e∪f)).
        apply proper_prod_inf;[|apply proper_star_inf,inf_cup_right].
        rewrite <- star_incr;apply inf_cup_left.
  Qed.    

  Lemma un_star : un⋆ ⩵ un.
  Proof.
    apply antisymmetry.
    - transitivity (un⋆⋅un);[rewrite right_unit;reflexivity|].
      apply ka_star_left_ind;rewrite left_unit;reflexivity.
    - apply star_incr.
  Qed.

  Lemma star_switch_side e : e⋆⋅e ⩵ e⋅ e⋆.
  Proof.
    apply antisymmetry.
    - transitivity (e⋆⋅e⋅e⋆).
      + rewrite <- one_inf_star at 3.
        rewrite right_unit;reflexivity.
      + rewrite <- (mon_assoc _ _ _).
        apply ka_star_left_ind.
        rewrite (star_incr e) at 2.
        rewrite ka_star_dup;reflexivity.
    - transitivity (e⋆⋅e⋅e⋆).
      + rewrite <- one_inf_star at 2.
        rewrite left_unit;reflexivity.
      + apply ka_star_right_ind.
        rewrite (star_incr e) at 2.
        rewrite ka_star_dup;reflexivity.
  Qed.

  Lemma ka_star_mid_split e : e⋆⋅e⋅e⋆ ≦ e⋆.
  Proof.
    etransitivity;[apply proper_prod_inf;[apply proper_prod_inf;
                                          [reflexivity|apply star_incr]|reflexivity]|].
    cut ((e ⋆ ⋅ e ⋆) ⋅ e ⋆ ⩵ e ⋆);[intros ->;reflexivity|].
    repeat rewrite ka_star_dup;reflexivity.
  Qed.

  Lemma ka_zero_star :  𝟬 ⋆ ⩵ 𝟭.
  Proof.
    apply antisymmetry.
    - transitivity (𝟬 ⋆ ⋅ 𝟭).
      + rewrite right_unit;reflexivity.
      + apply ka_star_left_ind.
        rewrite left_absorbing;apply zero_minimal.
    - apply one_inf_star.
  Qed.

End ka_facts.

Section bisemiring_is_semiring.
  Context {A} {eqA: relation A}.
  Context {equivA : @Equivalence A eqA}.
  Context {s p j : A -> A -> A} {u z : A}.
  Context {bsr : BiSemiRing A eqA s p j u z}.
  Lemma bisemiring_is_semiring : SemiRing A eqA s j u z.
  Proof.
    split.
    - apply bimon_seq.
    - apply bisemiring_add.
    - apply bisemiring_comm.
    - apply bisemiring_zero_seq.
    - apply bisemiring_left_distr.
    - apply bisemiring_right_distr.
  Qed.
  Lemma bisemiring_is_semiring_par : SemiRing A eqA p j u z.
  Proof.
    split.
    - apply bimon_par.
    - apply bisemiring_add.
    - apply bisemiring_comm.
    - apply bisemiring_zero_par.
    - apply bisemiring_par_distr.
    - intros.
      rewrite (bimon_comm (j a b)),bisemiring_par_distr.
      rewrite (bimon_comm c a), (bimon_comm c b).
      reflexivity.
  Qed.
End bisemiring_is_semiring.

Section bika_is_ka.
  Context {A} {eqA: relation A}.
  Context {equivA : @Equivalence A eqA}.
  Context `{BiKleeneAlgebra A eqA}.
  Lemma bika_is_ka : KleeneAlgebra A eqA.
  Proof.
    split.
    - apply bika_star_congr.
    - eapply bisemiring_is_semiring.
      Unshelve.
      + exact par.
      + exact bika_semiring.
    - apply bika_idem.
    - apply H.
    - apply H.
    - apply H.
  Qed.
End bika_is_ka.

Section powerset_biKA.
  Context {A} {eqA: relation A}.
  Context {equivA : @Equivalence A eqA}.
  
  Infix " ⩵ " := eqA (at level 80).
  
  Context `{Product A}`{ParProduct A}`{Un A}.
  Context {bimon: BiMonoid A eqA prod par un}.

  Definition SetBiKA := {f : A -> Prop | Proper (eqA ==> iff) f}.

  Definition member u (a : SetBiKA) := (proj1_sig a u).
  Infix " ∊ " := member (at level 80).

  Global Instance SetBiKA_eq : SemEquiv SetBiKA :=
    fun a b => forall u, u ∊ a <-> u ∊ b.
  Global Instance SetBiKA_inf : SemSmaller SetBiKA :=
    fun a b => forall u, u ∊ a -> u ∊ b.

  Global Instance member_Proper : Proper (eqA ==> sequiv ==> iff) member.
  Proof.
    intros u v E a b E'.
    transitivity (v ∊ a).
    - apply (proj2_sig a),E.
    - apply E'.
  Qed.
  
  Global Instance SetBiKA_eq_equiv : Equivalence sequiv.
  Proof.
    split.
    - intros (a,?) w;tauto.
    - intros (a,?) (b,?) E w;symmetry;apply E.
    - intros (a,?) (b,?) (c,?) E1 E2 w;rewrite (E1 _),(E2 _);reflexivity.
  Qed.

  Global Instance SetBiKA_inf_preorder : PreOrder ssmaller.
  Proof.
    split.
    - intros a w;tauto.
    - intros a b c E1 E2 w h;apply (E2 _),(E1 _),h.
  Qed.
  Global Instance SetBiKA_inf_partialorder : PartialOrder sequiv ssmaller.
  Proof.
    intros a b;unfold Basics.flip;split.
    - intros E;split;intros w h;apply E,h.
    - intros (h1&h2) w;split;[apply h1|apply h2].
  Qed.

  Lemma prod_internal (a b: SetBiKA) :
    Proper (eqA ==> iff) (fun w => exists u1 u2, w ⩵ u1 ⋅ u2 /\ u1 ∊ a /\ u2 ∊ b).
  Proof.
    intros u1 u2 E;split;intros (v1&v2&E'&I1&I2);exists v1,v2;repeat split;auto.
    - rewrite <-E;auto.
    - rewrite E;auto.
  Qed.
  Lemma par_internal (a b: SetBiKA) :
    Proper (eqA ==> iff) (fun w => exists u1 u2, w ⩵ u1 ∥ u2 /\ u1 ∊ a /\ u2 ∊ b).
  Proof.
    intros u1 u2 E;split;intros (v1&v2&E'&I1&I2);exists v1,v2;repeat split;auto.
    - rewrite <-E;auto.
    - rewrite E;auto.
  Qed.
  Lemma join_internal (a b: SetBiKA) :
    Proper (eqA ==> iff) (fun w => w ∊ a \/ w ∊ b).
  Proof.
    intros u v E.
    destruct a as (a&Pa),b as (b&Pb);simpl.
    rewrite (Pa _ _ E),(Pb _ _ E);reflexivity.
  Qed.
  Lemma un_internal : Proper (eqA ==> iff) (fun w => w ⩵ 𝟭).
  Proof. intros u v E;rewrite E;reflexivity. Qed.
    
  Lemma zero_internal : Proper (eqA ==> iff) (fun _ => False).
  Proof. intros ? ? ?;reflexivity. Qed.
  
  Global Instance SetBiKAProd : Product SetBiKA :=
    fun a b =>
      exist _ (fun w => exists u1 u2, w ⩵ u1 ⋅ u2 /\ u1 ∊ a /\ u2 ∊ b)
            (prod_internal a b).

  Global Instance SetBiKAPar : ParProduct SetBiKA :=
    fun a b =>
      exist _ (fun w => exists u1 u2, w ⩵ u1 ∥ u2 /\ u1 ∊ a /\ u2 ∊ b)
            (par_internal a b).
  
  Global Instance SetBiKAJoin : Join SetBiKA :=
    fun a b => exist _ (fun u => u ∊ a \/ u ∊ b) (join_internal a b).
  Global Instance SetBiKAUn : Un SetBiKA :=
    exist _ (fun u => u ⩵ 𝟭) un_internal.
  Global Instance SetBiKAZero : Zero SetBiKA :=
    exist _ (fun _ => False) zero_internal.
  
  
  Lemma star_internal a : Proper (eqA ==> iff) (fun u => exists n, u ∊ (a ^ n)).
  Proof. intros u1 u2 E;split;intros (n&I);exists n;apply (proj2_sig (a^n) _ _ E),I. Qed.

  Global Instance SetBiKAStar : Star SetBiKA :=
    fun a => exist _ (fun u => exists n, u ∊ (a ^ n)) (star_internal a).

  Global Instance SetBiKA_bisemiring : BiSemiRing SetBiKA sequiv prod par join un zero.
  Proof.
    split.
    - split.
      + split.
        * intros (a,?) (b,?) E (a',?) (b',?) E' w;split.
          -- intros (u1&u2&Eu&E1&E2);exists u1,u2.
             apply E in E1;apply E' in E2;tauto.
          -- intros (u1&u2&Eu&E1&E2);exists u1,u2.
             apply E in E1;apply E' in E2;tauto.
        * intros a b c w;split.
          -- intros (u1&?&E1&I1&u2&u3&E2&I2&I3).
             exists (u1⋅u2),u3;repeat split;auto.
             ++ rewrite E1,E2;apply mon_assoc.
             ++ exists u1,u2;repeat split;auto.
                reflexivity.
          -- intros (?&u3&E1&(u1&u2&E2&I1&I2)&I3).
             exists u1,(u2⋅u3);repeat split;auto.
             ++ rewrite E1,E2;symmetry;apply mon_assoc.
             ++ exists u2,u3;repeat split;auto.
                reflexivity.
        * split;intros a w;split.
          -- intros (u1&u2&E1&E2&I).
             eapply (proj2_sig a);[|eauto].
             rewrite E1,E2,left_unit;reflexivity.
          -- intros I;exists 𝟭,w.
             repeat split;auto.
             ++ rewrite left_unit;reflexivity.
             ++ simpl;reflexivity.
          -- intros (u1&u2&E1&I&E2).
             eapply (proj2_sig a);[|eauto].
             rewrite E1,E2,right_unit;reflexivity.
          -- intros I;exists w,(𝟭:A).
             repeat split;auto.
             ++ rewrite right_unit;reflexivity.
             ++ simpl;reflexivity.
      + split.
        * intros a b E a' b' E' w;split.
          -- intros (u1&u2&Eu&E1&E2);exists u1,u2.
             apply E in E1;apply E' in E2;tauto.
          -- intros (u1&u2&Eu&E1&E2);exists u1,u2.
             apply E in E1;apply E' in E2;tauto.
        * intros a b c w;split.
          -- intros (u1&?&E1&I1&u2&u3&E2&I2&I3).
             exists (u1∥u2),u3;repeat split;auto.
             ++ rewrite E1,E2;apply mon_assoc.
             ++ exists u1,u2;repeat split;auto.
                reflexivity.
          -- intros (?&u3&E1&(u1&u2&E2&I1&I2)&I3).
             exists u1,(u2∥u3);repeat split;auto.
             ++ rewrite E1,E2;symmetry;apply mon_assoc.
             ++ exists u2,u3;repeat split;auto.
                reflexivity.
      * split;intros a w;split.
          -- intros (u1&u2&E1&E2&I).
             eapply (proj2_sig a);[|eauto].
             rewrite E1,E2,left_unit;reflexivity.
          -- intros I;exists 𝟭,w.
             repeat split;auto.
             ++ rewrite left_unit;reflexivity.
             ++ simpl;reflexivity.
          -- intros (u1&u2&E1&I&E2).
             eapply (proj2_sig a);[|eauto].
             rewrite E1,E2,right_unit;reflexivity.
          -- intros I;exists w,(𝟭:A).
             repeat split;auto.
             ++ rewrite right_unit;reflexivity.
             ++ simpl;reflexivity.
      + intros a b w;split;intros (u1&u2&->&I1&I2);rewrite (bimon_comm _);exists u2,u1;
          repeat split;auto||reflexivity.
    - split.
      + intros a b E a' b' E' w;split;intros [I|I];(left;apply E,I)||(right;apply E',I).
      + intros a b c w;unfold join,SetBiKAJoin;simpl;tauto.
      + split;intros a w;unfold join,SetBiKAJoin,zero,SetBiKAZero;simpl;tauto.
    - intros a b w;unfold join,SetBiKAJoin;simpl;tauto.
    - split;intros a w;unfold prod,SetBiKAProd,zero,SetBiKAZero;simpl;firstorder.
    - split;intros a w;unfold par,SetBiKAPar,zero,SetBiKAZero;simpl;firstorder.
    - intros a b c w;split.
      + intros (u1&u2&->&I1&[I2|I2]);[left|right];exists u1,u2;repeat split;auto||reflexivity.
      + intros [(u1&u2&->&I1&I2)|(u1&u2&->&I1&I2)];exists u1,u2;
          repeat split;reflexivity||auto;[left|right];auto.
    - intros a b c w;split.
      + intros (u1&u2&->&[I1|I1]&I2);[left|right];exists u1,u2;repeat split;auto||reflexivity.
      + intros [(u1&u2&->&I1&I2)|(u1&u2&->&I1&I2)];exists u1,u2;
          repeat split;reflexivity||auto;[left|right];auto.
    - intros a b c w;split.
      + intros (u1&u2&->&I1&[I2|I2]);[left|right];exists u1,u2;repeat split;auto||reflexivity.
      + intros [(u1&u2&->&I1&I2)|(u1&u2&->&I1&I2)];exists u1,u2;
          repeat split;reflexivity||auto;[left|right];auto.
  Qed.

  
  Global Instance SetBiKA_biKA : BiKleeneAlgebra SetBiKA sequiv.
  Proof.
    split.
    - intros a b E w;split;intros (n&I);exists n.
      + rewrite <- E;assumption.
      + rewrite E;assumption.
    - apply SetBiKA_bisemiring.
    - intros a w;unfold join,SetBiKAJoin;simpl;tauto.
    - intros a w;split;[intros I;right;auto|intros [I|I];[|apply I]].
      destruct I as [->|(u1&u2&->&I1&n&I2)].
      + exists 0;simpl;reflexivity.
      + exists (S n),u1,u2;repeat split;auto||reflexivity.
    - intros a b E w;split;[intros I;right;auto|intros [I|I];[|apply I]].
      destruct I as (u1&u2&->&(n&I1)&I2).
      revert u1 u2 I1 I2;induction n;intros u1 u2 I1 I2.
      + rewrite I1,left_unit;auto.
      + destruct I1 as (v1&v2&->&I1&I1').
        rewrite <- (mon_assoc _).
        apply E;left;exists v1,(v2⋅u2);repeat split;auto||reflexivity.
    - intros a b E w;split;[intros I;right;auto|intros [I|I];[|apply I]].
      destruct I as (u1&u2&->&I1&n&I2).
      revert u1 u2 I1 I2;induction n;intros u1 u2 I1 I2.
      + rewrite I2,right_unit;auto.
      + rewrite Power_last in I2;destruct I2 as (v1&v2&->&I2&I2').
        rewrite (mon_assoc _).
        apply E;left;exists (u1⋅v1),v2;repeat split;auto||reflexivity.
  Qed.

  Lemma SetBiKA_inf_is_impl a b : leqA sequiv a b <-> a ≲ b.
  Proof.
    unfold leqA;split.
    - intros -> w I;left;auto.
    - intros I w;split.
      + intro I';right;auto.
      + intros [I'|I'].
        * apply I,I'.
        * auto.
  Qed.

  (** * Finite elements *)

  Definition mem (L : list A) := fun x => exists y, y ∈ L /\ y ⩵ x.
  
  Lemma list_internal L : Proper (eqA ==> iff) (mem L).
  Proof.
    intros x y E;split;intros (z&Iz&Ez);exists z;rewrite Ez at 2;rewrite E;
      split;assumption||reflexivity.
  Qed.
      
  Definition lift L : SetBiKA := exist _ (mem L) (list_internal L).

  Notation " ⟨ L ⟩ " := (lift L).

  Global Instance infLang : SemSmaller (list A) :=
    fun L M => forall x, x ∈ L -> exists y, y ∈ M /\ y ⩵ x.
  
  Global Instance eqLang : SemEquiv (list A) :=
    fun L M => L ≲ M /\ M ≲ L.
  
  Global Instance infLang_PreOrder : PreOrder ssmaller.
  Proof.
    split.
    - intros L x I;exists x;split;assumption||reflexivity.
    - intros L M N E1 E2 x I.
      apply E1 in I as (y&I&E).
      setoid_rewrite <-E.
      apply E2,I.
  Qed.
  Global Instance eqLang_Equiv : Equivalence sequiv.
  Proof.
    repeat split.
    - reflexivity.
    - reflexivity.
    - destruct H4;tauto.
    - destruct H4;tauto.
    - transitivity y;[apply H4|apply H5].
    - transitivity y;[apply H5|apply H4].
  Qed.
  Global Instance infLang_PartialOrder : PartialOrder sequiv ssmaller.
  Proof. repeat split;apply H4. Qed.

  Lemma lift_iso l m : l ≃ m <-> ⟨l⟩ ≃ ⟨m⟩.
  Proof.
    split.
    - intros (h1&h2);intro x;unfold member;simpl;unfold mem.
      split;intros (y&Iy&Ey);setoid_rewrite <- Ey;[apply h1|apply h2];apply Iy.
    - intros h;split;intros x Ix;apply h;exists x;split;assumption||reflexivity.
  Qed.

  Global Instance prod_list : Product (list A) := (@lift_prod A prod).
  Global Instance par_list : ParProduct (list A) := (@lift_prod A par).
  Global Instance join_list : Join (list A) := (@app A).
  Global Instance unit_list : Un (list A) := [𝟭].
  Global Instance zero_list : Zero (list A) := [].

  Lemma prod_list_eq l m : ⟨l ⋅ m⟩ ≃ ⟨l⟩⋅⟨m⟩.
  Proof.
    intro a;split.
    - intros (b&Ib&<-);unfold prod,prod_list in Ib.
      apply lift_prod_spec in Ib as (b1&b2&Ib1&Ib2&->).
      exists b1,b2;repeat split.
      + reflexivity.
      + exists b1;split;assumption||reflexivity.
      + exists b2;split;assumption||reflexivity.
    - intros (a1&a2&->&(b1&I1&<-)&b2&I2&<-).
      exists (b1⋅b2);split;[apply lift_prod_spec;exists b1,b2;tauto|reflexivity].
  Qed.
      
  Lemma par_list_eq l m : ⟨l ∥ m⟩ ≃ ⟨l⟩∥⟨m⟩.
  Proof.
    intro a;split.
    - intros (b&Ib&<-);unfold par,par_list in Ib.
      apply lift_prod_spec in Ib as (b1&b2&Ib1&Ib2&->).
      exists b1,b2;repeat split.
      + reflexivity.
      + exists b1;split;assumption||reflexivity.
      + exists b2;split;assumption||reflexivity.
    - intros (a1&a2&->&(b1&I1&<-)&b2&I2&<-).
      exists (b1∥b2);split;[apply lift_prod_spec;exists b1,b2;tauto|reflexivity].
  Qed.

  Lemma join_list_eq l m : ⟨l∪m⟩ ≃ ⟨l⟩∪⟨m⟩.
  Proof.
    intro a;split.
    - intros (b&Ib&<-).
      apply in_app_iff in Ib as [Ib|Ib];[left|right];exists b;split;assumption||reflexivity.
    - intros [I|I];destruct I as (b&Ib&<-);exists b;split;try reflexivity;
        apply in_app_iff;[left|right];assumption.
  Qed.
        
  Lemma unit_list_eq : ⟨𝟭⟩ ≃ 𝟭.
  Proof.
    intro a;split.
    - intros (b&[<-|F]&<-).
      + simpl;reflexivity.
      + simpl in F;tauto.
    - intros ->;exists 𝟭;split;[left|];reflexivity.
  Qed.

  Lemma zero_list_eq : ⟨𝟬⟩ ≃ 𝟬.
  Proof. intros a;split;simpl;unfold mem;simpl;firstorder. Qed.
    
  Global Instance ListBiSemiRing_bisemiring :
    BiSemiRing (list A) sequiv prod par join un zero.
  Proof.
    split.
    - split.
      + split.
        * intros x y E1 z t E2.
          rewrite lift_iso in *;repeat rewrite prod_list_eq.
          rewrite E1,E2;reflexivity.
        * intros x y z.
          rewrite lift_iso in *;repeat rewrite prod_list_eq.
          apply mon_assoc.
        * split;intro x;apply lift_iso;rewrite prod_list_eq,unit_list_eq.
          -- apply left_unit.
          -- apply right_unit.
      + split.
        * intros x y E1 z t E2.
          rewrite lift_iso in *;repeat rewrite par_list_eq.
          rewrite E1,E2;reflexivity.
        * intros x y z.
          rewrite lift_iso in *;repeat rewrite par_list_eq.
          apply mon_assoc.
        * split;intro x;apply lift_iso;rewrite par_list_eq,unit_list_eq.
          -- apply left_unit.
          -- apply right_unit.
      + intros x y;rewrite lift_iso in *;repeat rewrite par_list_eq;apply bimon_comm.
    - split.
      * intros x y E1 z t E2.
        rewrite lift_iso in *;repeat rewrite join_list_eq.
        rewrite E1,E2;reflexivity.
      * intros x y z.
        rewrite lift_iso in *;repeat rewrite join_list_eq.
        apply mon_assoc.
      * split;intro x;apply lift_iso;rewrite join_list_eq,zero_list_eq.
        -- apply left_unit.
        -- apply right_unit.
    - intros x y;apply lift_iso;repeat rewrite join_list_eq;apply bisemiring_comm.
    - split;intro x;apply lift_iso;rewrite prod_list_eq,zero_list_eq.
      + apply left_absorbing.
      + apply right_absorbing.
    - split;intro x;apply lift_iso;rewrite par_list_eq,zero_list_eq.
      + apply left_absorbing.
      + apply right_absorbing.
    - intros x y z;apply lift_iso;repeat rewrite prod_list_eq||rewrite join_list_eq.
      apply bisemiring_left_distr.
    - intros x y z;apply lift_iso;repeat rewrite prod_list_eq||rewrite join_list_eq.
      apply bisemiring_right_distr.
    - intros x y z;apply lift_iso;repeat rewrite par_list_eq||rewrite join_list_eq.
      apply bisemiring_par_distr.
  Qed.
  
  Global Instance ListBiSemiRing_idempotent : @Idempotent _ sequiv join.
  Proof. intros x;apply lift_iso;repeat rewrite join_list_eq;apply bika_idem. Qed.

End powerset_biKA.
Arguments SetBiKA : clear implicits.
Infix " ∊ " := member (at level 80).
  
Section morph.
  
  Context {A : Type} {eqA: relation A}.
  Context {equivA : @Equivalence A eqA}.
  
  Infix " =A " := eqA (at level 80).
  
  Context {joinA: Join A}{seqA: Product A}{parA:ParProduct A}{zA: Zero A}{uA:Un A}
          {sA:Star A}.
  
  Context {B : Type} {eqB: relation B}.
  Context {equivB : @Equivalence B eqB}.
  
  Infix " =B " := eqB (at level 80).
  
  Context {joinB: Join B}{seqB: Product B}{parB:ParProduct B}{zB: Zero B}{uB:Un B}
          {sB:Star B}.

  Class biKA_morph (g : A -> B) :=
    {
      morph_eq : Proper (eqA ==> eqB) g;
      morph_1 : g 𝟭 =B 𝟭;
      morph_0 : g 𝟬 =B 𝟬;
      morph_prod : forall b1 b2, g (b1 ⋅ b2) =B g b1 ⋅ g b2;
      morph_par : forall b1 b2, g (b1 ∥ b2) =B g b1 ∥ g b2;
      morph_join : forall b1 b2, g (b1 ∪ b2) =B g b1 ∪ g b2;
      morph_star : forall b, g (b⋆) =B g b⋆;
    }.
End morph.

Arguments biKA_morph : clear implicits.
Arguments biKA_morph {A} eqA {joinA seqA parA zA uA sA B} eqB {joinB seqB parB zB uB sB} g.

(* Section iso_biKA. *)
(*   Context {A : Type} {eqA: relation A}. *)
(*   Context {equivA : @Equivalence A eqA}. *)
  
(*   Infix " =A " := eqA (at level 80). *)
  
(*   Context {j: Join A}{seq: Product A}{par:ParProduct A}{z: Zero A}{u:Un A}{s:Star A}. *)
(*   Context {biKA: BiKleeneAlgebra A eqA}. *)

  
(*   Context {B : Type} {eqB: relation B}. *)
(*   Context {equivB : @Equivalence B eqB}. *)
  
(*   Infix " =B " := eqB (at level 80). *)
  
(*   Context {joinB: Join B}{seqB: Product B}{parB:ParProduct B}{zB: Zero B}{uB:Un B} *)
(*           {sB:Star B}. *)

(*   Context {f : A -> B} {g : B -> A}. *)
(*   Hypothesis fg : forall b, f (g b) =B b. *)
(*   Hypothesis gf : forall a, g (f a) =A a. *)
  
(*   Hypothesis g_morph : biKA_morph eqB eqA g. *)
(*   Hypothesis f_morph : biKA_morph eqA eqB f. *)
  
(*   Theorem BiKA_B : BiKleeneAlgebra B eqB. *)
(*   Proof. *)
(*     split. *)
(*     - intros b1 b2 E. *)
(*       etransitivity;[|apply fg]. *)
(*       etransitivity;[symmetry;apply fg|]. *)
(*       apply morph_eq. *)
(*       repeat rewrite morph_star. *)
(*       apply morph_eq in E;rewrite E;reflexivity. *)
(*     - repeat split. *)
(*       + intros b1 b2 E1 b1' b2' E2. *)
(*         etransitivity;[|apply fg]. *)
(*         etransitivity;[symmetry;apply fg|]. *)
(*         apply morph_eq. *)
(*         repeat rewrite morph_prod. *)
(*         apply morph_eq in E1;apply morph_eq in E2. *)
(*         destruct biKA. *)
(*         destruct bika_semiring0. *)
(*         destruct bisemiring_bimon0. *)
(*         destruct bimon_seq0. *)
(*         apply mon_congr0;auto. *)
(*       +  *)
        
(*         apply mon_congr. *)
(*         reflexivity. *)
        
    

        
(* Lemma iso_biKA   : *)
(*   () -> *)
(*   (forall a, g (f a) eqA a) -> *)
(*    -> *)
(*   (forall b1 b2, . *)
         
         