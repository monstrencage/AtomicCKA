Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PeanoNat tools algebra Bool bindings types_of_bsp.
Require Import brack_terms bsp_terms.

Section encoding.
  Context {X : Set} {decX : decidable_set X}.
  
  Notation " ⦃ " := (sp_var (inr Open)).
  Notation " ⦄ " := (sp_var (inr Close)).
  Notation VOpen := (sp_var (inr Open)).
  Notation VClose := (sp_var (inr Close)).
  Notation X' := (X + brack)%type.

  Fixpoint unbox (s : bsp_terms X) : sp_terms X' :=
    match s with
    | bsp_seq t1 t2 => unbox t1 ⋅ unbox t2
    | bsp_par t1 t2 => unbox t1 ∥ unbox t2
    | bsp_var x => sp_var (inl x)
    | bsp_unit => 𝟭
    | bsp_box s => ⦃⋅unbox s⋅⦄
    end.

  Global Instance unbox_proper : Proper (bsp_eq_bis ==> equiv) unbox.
  Proof. intros s t E;induction E;simpl;eauto. Qed.

  Corollary unbox_clean_proper : Proper (equiv ==> equiv) (fun s => unbox (bsp_clean s)).
  Proof. intros s t E;apply unbox_proper,bsp_clean_proper,E. Qed.

  Lemma unbox_bind s : sp_bind (unbox s) ∈ [ℯ;𝒷].
  Proof.
    induction s;simpl.
    - destruct IHs1 as [<-|[<-|F1]],IHs2 as [<-|[<-|F2]];try tauto.
    - destruct IHs1 as [<-|[<-|F1]],IHs2 as [<-|[<-|F2]];try tauto.
    - tauto.
    - destruct IHs as [<-|[<-|F]];try tauto.
    - tauto.
  Qed.

  Definition T := (option (sp_terms X') * bsp_terms X * option (sp_terms X'))%type.

  Definition π1 : T -> option (sp_terms X') := fun x => fst (fst x).
  Definition π2 : T -> bsp_terms X := fun x => snd (fst x).
  Definition π3 : T -> option (sp_terms X') := fun x => snd x.
  
  Instance equiv_opt : Equiv (option (sp_terms X')) :=
    fun x y =>
      match x,y with
      | None,None => True
      | Some _,None | None,Some _ => False
      | Some s,Some t => s ≡ t
      end.

  Instance equiv_opt_equivalence : Equivalence equiv.
  Proof.
    split;intro;intros.
    - destruct x;unfold equiv,equiv_opt;[reflexivity|tauto].
    - destruct x,y;unfold equiv,equiv_opt in *;auto||tauto.
    - destruct x,y,z;unfold equiv,equiv_opt in *;try tauto.
      etransitivity;eassumption.
  Qed.
  Instance equiv_T : Equiv T :=
    fun x y => π1 x ≡ π1 y /\ π2 x ≡ π2 y /\ π3 x ≡ π3 y.

  Instance equiv_T_equivalence : Equivalence equiv.
  Proof.
    split;intro;intros.
    - destruct x as ((x1&x2)&x3);repeat split;reflexivity.
    - destruct H as (h1&h2&h3),x as ((x1&x2)&x3), y as ((y1&y2)&y3);repeat split;symmetry;
        assumption.
    - destruct H as (h1&h2&h3),H0 as (h'1&h'2&h'3),
                                     x as ((x1&x2)&x3), y as ((y1&y2)&y3),z as((z1&z2)&z3);
        simpl in *;repeat split;simpl;etransitivity;eassumption.
  Qed.

  
  Definition prod_T f s t : T :=
    if open (sp_bind s) <? close (sp_bind t)
    then
      match f t with
      | (None,_,_) => (None,𝟭,None)
      | (Some t1,t2,t3) => (Some (s⋅t1),t2,t3)
      end
    else
      if close (sp_bind t) <? open (sp_bind s) 
      then 
        match f s with
        | (_,_,None) => (None,𝟭,None)
        | (s1,s2,Some s3) => (s1,s2,Some (s3⋅t))
        end
      else 
        match f s,f t with
        | (s1,s2,None),(None,t2,t3) => (s1,s2⋅t2,t3)
        | (s1,s2,Some s3),(Some t1,t2,t3) => (s1,s2⋅▢(π2 (f (sp_clean (s3⋅t1))))⋅t2,t3)
        | _,_ =>  (None,𝟭,None)
      end.

  Fixpoint rebox k s : T :=
    match k with
    | 0 => (None,𝟭,None)
    | S k =>
      match s with
      | sp_par s1 s2 => (None,π2 (rebox k s1)∥ π2 (rebox k s2),None)
      | VOpen => (None,𝟭,Some 𝟭)
      | VClose => (Some 𝟭,𝟭,None)
      | sp_var(inl x) => (None,bsp_var x,None)
      | sp_seq s1 s2 => prod_T (rebox k) s1 s2
      | sp_unit => (None,𝟭,None)
      end
    end.

  Instance size_T : Size T:=
    fun t => match t with
          | (None,s,None) => ⎢s⎥
          | (Some s',s,None) | (None,s,Some s') => S ⎢s'⎥ + ⎢s⎥
          | (Some s1,s2,Some s3) => S ⎢s1⎥ + ⎢s2⎥ + S ⎢s3⎥
          end.
  Remark size_T_0 s : ⎢(None,s,None)⎥=⎢s⎥.
  Proof. reflexivity. Qed.
  Remark size_T_1 s t : ⎢(Some t,s,None)⎥=S⎢t⎥ + ⎢s⎥.
  Proof. reflexivity. Qed.
  Remark size_T_2 s t : ⎢(None,s,Some t)⎥=S⎢t⎥ + ⎢s⎥.
  Proof. reflexivity. Qed.
  Remark size_T_3 s1 s2 s3: ⎢(Some s1,s2,Some s3)⎥=S ⎢s1⎥ + ⎢s2⎥ + S ⎢s3⎥.
  Proof. reflexivity. Qed.
  Hint Rewrite size_T_0 size_T_1 size_T_2 size_T_3 : simpl_typeclasses.

  Definition T_bind : T -> binding :=
    fun t => match t with
          | (None,s,None) => 𝒷
          | (Some s',s,None) => (* if sp_bind s' =?= ↯ then ↯ *)
                               (* else  *) Bnd (S (close (sp_bind s'))) 0 
          | (None,s,Some s') =>  (* if sp_bind s' =?= ↯ then ↯ *)
                                (* else *) Bnd 0 (S (open (sp_bind s')))
          | (Some s1,s2,Some s3) =>  (* if sp_bind (s1⋅s3) =?= ↯ then ↯ *)
                                    (* else *) Bnd (S (close (sp_bind s1)))
                                             (S (open (sp_bind s3)))
          end.

  Definition good_T (t : T) :=
    match t with
    | (Some s,_,None) => sp_bind s <> ↯ /\ open (sp_bind s) = 0
    | (None,_,Some s) => sp_bind s <> ↯ /\ close (sp_bind s) = 0
    | (Some s,_,Some s') => sp_bind s <> ↯ /\ sp_bind s' <> ↯
                           /\ open (sp_bind s) = 0
                           /\ close (sp_bind s') = 0
    | _ => True
    end.

  Lemma cases_seq_prod s t :
    T_bind s <> ↯ ->
    T_bind t <> ↯ ->
    good_T s ->
    good_T t ->
    open (T_bind s) < close (T_bind t) /\
    (exists t' : sp_terms X', π1 t = Some t') \/
    close (T_bind t) < open (T_bind s) /\
    (exists s' : sp_terms X', π3 s = Some s') \/
    close (T_bind t) = open (T_bind s) /\
    ((exists s' t' : sp_terms X', π3 s = Some s' /\ π1 t = Some t') \/
     π3 s = None /\ π1 t = None).
  Proof.
    destruct_leb (open (T_bind s)) (close (T_bind t));
      [destruct_leb (close (T_bind t)) (open (T_bind s))|];
      [right;right|left|right;left];(split;[lia|]).
    - destruct s as ((k1&k2)&k3), t as ((l1&l2)&l3).
      unfold π1,π3;simpl.
      assert (E: open (T_bind (k1, k2, k3)) = close (T_bind (l1, l2, l3)))
        by (revert L L0;clear;lia);clear L L0.
      revert E;simpl;destruct k3,l1;simpl.
      + intros _;left;eexists;eexists;split;reflexivity.
      + intros E;exfalso;revert E.
        destruct k1,l3;simpl;discriminate.
      + intros E;exfalso;revert E.
        destruct k1,l3;simpl;discriminate.
      + intros _;right;split;reflexivity.
    - revert L0.
      destruct t as ((k1&k2)&k3);unfold π1;simpl.
      destruct k1;[intros _;eexists;reflexivity|intro F;exfalso;revert F].
      destruct k3;simpl.
      + destruct_eqX (sp_bind s0) ↯;simpl;clear;lia.
      + clear;lia.
    - revert L.
      destruct s as ((k1&k2)&k3);unfold π3;simpl.
      destruct k3;[intros _;eexists;reflexivity|intro F;exfalso;revert F].
      destruct k1;simpl.
      + destruct_eqX (sp_bind s) ↯;simpl;clear;lia.
      + clear;lia.
  Qed.
    
    
  Lemma rebox_invariants k s :
    ⎢s⎥ <= k -> is_sp_clean s -> sp_bind s <> ↯ ->
    rebox k s = rebox ⎢s⎥ s
    /\ ⎢rebox k s⎥ <= ⎢s⎥
    /\ T_bind (rebox k s) = sp_bind s
    /\ good_T (rebox k s).
  Proof.
    remember k as K;rewrite HeqK.
    intros h;assert (h__size: ⎢s⎥ <= k <= K) by lia;clear HeqK h.
    revert k s h__size;induction K;intros k s h__size h__clean h__bind;
      [apply is_sp_clean_sp_size in h__clean;lia|].
    destruct k;[apply is_sp_clean_sp_size in h__clean;lia|].
    case_eq ⎢s⎥;
      [apply is_sp_clean_sp_size in h__clean;simpl in *;lia
      |intros n' En'].
    destruct s as [s1 s2 |s1 s2| [x|[]] |];rsimpl in *.
    - assert (⎢s1⎥ <= k <= K /\ is_sp_clean s1 /\ sp_bind s1 <> ↯) as (S1&C1&B1)
          by (split;[|split];
              [destruct h__clean as (_&h);apply is_sp_clean_sp_size in h;simpl in *;lia
              |destruct h__clean as (h&_);apply h
              |simpl in h__bind;intros E;rewrite E in h__bind;tauto]).
      assert (⎢s2⎥ <= k <= K /\ is_sp_clean s2 /\ sp_bind s2 <> ↯) as (S2&C2&B2)
          by (split;[|split];
              [destruct h__clean as (h&_);apply is_sp_clean_sp_size in h;simpl in *;lia
              |destruct h__clean as (_&h);apply h
              |simpl in h__bind;intros E;rewrite E,right_absorbing in h__bind;tauto]).
      assert (⎢s1⎥ <= n' <= K) as S1'
          by (destruct h__clean as (_&h);apply is_sp_clean_sp_size in h;simpl in *;lia).
      assert (⎢s2⎥ <= n' <= K) as S2'
          by (destruct h__clean as (h&_);apply is_sp_clean_sp_size in h;simpl in *;lia).
      destruct (IHK k s1) as (R1&SR1&BR1&G1);auto.
      destruct (IHK k s2) as (R2&SR2&BR2&G2);auto.
      destruct (IHK n' s1) as (R'1&_);auto.
      destruct (IHK n' s2) as (R'2&_);auto.
      destruct (@cases_seq_prod (rebox k s1) (rebox k s2)) as [(L&E)|[(L&E)|(L&E)]];
        auto.
      * rewrite BR1;assumption.
      * rewrite BR2;assumption.
      * simpl;unfold prod_T.
        rewrite BR1,BR2 in L. 
        pose proof L as h; apply Nat.ltb_lt in h as ->.
        rewrite R'2,<-R2.
        remember (rebox k s2) as T2.
        destruct T2 as (([t4|]&t5)&t6);
          [clear E|destruct E as (?&E);unfold π1 in E;discriminate].
        simpl;split;[reflexivity|].
        destruct t6;(split;[|split]).
        -- rewrite <- En';simpl;rewrite <- SR2;rsimpl;clear;lia.
        -- rewrite <- BR2;simpl.
           revert BR2;simpl.
           destruct (sp_bind s1) as [| |];simpl.
           --- rewrite left_unit;reflexivity.
           --- exfalso;apply B1;reflexivity.
           --- unfold prod,SeqBind.
               destruct G2 as (g1&g2&g3&g4).
               destruct (sp_bind t4) as [| |];simpl.
               +++ intros E';revert L;simpl.
                   rewrite <- E';simpl;clear.
                   intros L;replace n0 with 0 by lia.
                   f_equal;lia.
               +++ exfalso;apply g1;reflexivity.
               +++ intros E';revert L;simpl.
                   rewrite <- E';simpl;clear.
                   destruct n0;intro;f_equal;lia.
        -- rewrite bind_error_seq.
           destruct G2 as (g1&g2&g3&g4).
           rewrite open_prod by (rewrite bind_error_seq;revert B1 g1;clear;tauto).
           rewrite g3,g4.
           repeat split;[revert B1 g1;clear;tauto|assumption|].
           rewrite <- BR2 in L.
           simpl in L.
           revert L;clear;lia.
        -- rewrite <- En';simpl;rewrite <- SR2;rsimpl;clear;lia.
        -- destruct G2 as (g1&g2).
           rewrite close_prod by (rewrite bind_error_seq;revert B1 g1;clear;tauto).
           rewrite <- BR2;simpl.
           destruct (sp_bind s1).
           ++ repeat rewrite left_unit;f_equal;simpl;clear;lia.
           ++ exfalso;apply B1;reflexivity.
           ++ unfold prod,SeqBind;revert L;rewrite <- BR2;simpl.
              intro L;f_equal;[|revert L;clear;lia].
              destruct n0;revert L;clear;lia.
        -- rewrite bind_error_seq.
           destruct G2 as (g1&g2).
           rewrite open_prod by (rewrite bind_error_seq;revert B1 g1;clear;tauto).
           rewrite g2.
           repeat split;[revert B1 g1;clear;tauto|].
           rewrite <- BR2 in L.
           simpl in L.
           revert L;clear;lia.
      * simpl;unfold prod_T.
        rewrite BR1,BR2 in L.
        pose proof L as h; apply Nat.ltb_lt in h as ->.
        pose proof L as h; apply Nat.lt_asymm,Nat.ltb_nlt in h as ->. 
        rewrite R'1,<-R1;simpl.
        remember (rebox k s1) as T1.
        destruct T1 as ((t1&t2)&[t3|]);
          [clear E|destruct E as (?&E);unfold π3 in E;simpl in E;discriminate].
        simpl;split;[reflexivity|].
        destruct t1;split.
        -- rewrite <- En';simpl;rewrite <- SR1;rsimpl;clear;lia.
        -- rewrite <- BR1;simpl.
           revert BR1;simpl.
           destruct G1 as (g1&g2&g3&g4).
           rewrite open_prod by (rewrite bind_error_seq;revert B2 g2;clear;tauto).
           rewrite close_prod by (rewrite bind_error_seq;revert B2 g2;clear;tauto).
           intro BR1;revert L;rewrite <- BR1;simpl.
           rewrite g3.
           rewrite g4.
           rewrite bind_error_seq.
           revert B2 g1 g2;clear.
           firstorder.
           destruct (sp_bind s2).
           ++ rewrite right_unit;simpl;f_equal;lia.
           ++ exfalso;apply B2;reflexivity.
           ++ unfold prod,SeqBind;simpl in H; f_equal;simpl.
              ** lia.
              ** destruct n;lia.
        -- rewrite <- En';simpl;rewrite <- SR1;rsimpl;clear;lia.
        -- rewrite <- BR1;simpl.
           revert BR1;simpl.
           destruct G1 as (g1&g2).
           rewrite open_prod by (rewrite bind_error_seq;revert B2 g1;clear;tauto).
           rewrite close_prod by (rewrite bind_error_seq;revert B2 g1;clear;tauto).
           intro BR1;revert L;rewrite <- BR1;simpl.
           rewrite g2.
           rewrite bind_error_seq.
           revert B2 g1 g2;clear.
           firstorder.
           destruct (sp_bind s2).
           ++ rewrite right_unit;simpl;f_equal;lia.
           ++ exfalso;apply B2;reflexivity.
           ++ unfold prod,SeqBind;simpl in H; f_equal;simpl.
              ** lia.
              ** destruct n;lia.
      * simpl;unfold prod_T.
        rewrite BR1,BR2 in L.
        rewrite L,Nat.ltb_irrefl.
        rewrite R'1,<-R1.
        rewrite R'2,<-R2.
        remember (rebox k s1) as T1.
        remember (rebox k s2) as T2.
        destruct T1 as ((t1&t2)&[t3|]);destruct T2 as (([t4|]&t5)&t6);
          (destruct E as [(?&?&E1&E2)|(E1&E2)];unfold π1,π3 in *;discriminate)||clear E.
        -- assert (Ln'k : n' <= k) by (rewrite En' in h__size;revert h__size;clear;lia).
           assert (h1 : ⎢t3⋅t4⎥ <= n')
             by (revert En';simpl;revert SR1 SR2;rsimpl;destruct t1,t6;rsimpl;clear;lia).
           rewrite (sp_size_proper (sp_clean_eq _)) in h1.
           assert (h2: sp_bind (t3⋅t4) <> ↯)
             by (simpl;rewrite bind_error_seq;revert G1 G2;
                 destruct t1,t6;simpl;clear;tauto).
           rewrite (sp_bind_proper (sp_clean_eq _)) in h2.
           destruct (sp_clean_is_sp_clean (t3⋅t4))
             as [E|C].
           ++ rewrite E.
              pose proof (sp_clean_eq (t3⋅t4)) as EE.
              rewrite E in EE.
              apply sp_size_unit in EE;simpl in EE.
              assert (⎢t3⎥ = 0 /\ ⎢t4⎥ = 0) as (Ut3&Ut4)
                  by (revert EE;clear;rsimpl;lia).
              apply sp_size_unit in Ut3.
              apply sp_size_unit in Ut4.
              clear EE.
              replace (π2 (rebox k 𝟭)) with 𝟭 by (destruct k;reflexivity).
              replace (π2 (rebox n' 𝟭)) with 𝟭 by (destruct n';reflexivity).
              repeat split.
              ** rewrite <- En';simpl;rewrite <- SR1,<-SR2;simpl.
                 destruct t1,t6;rsimpl;clear;lia.
              ** rewrite <- BR1,<-BR2;simpl.
                 apply sp_binding_unit in Ut3 as ->.
                 apply sp_binding_unit in Ut4 as ->.
                 destruct t1,t6.
                 --- unfold prod,SeqBind;f_equal;simpl;clear;lia.
                 --- unfold prod,SeqBind;f_equal;simpl;clear;lia.
                 --- unfold prod,SeqBind;f_equal;simpl;clear;lia.
                 --- unfold prod,SeqBind;f_equal;simpl;clear;lia.
              ** revert G1 G2;clear;destruct t1,t6;simpl;tauto.
           ++ destruct (IHK k (sp_clean (t3 ⋅ t4))) as (H1&H2&H3&GG);
                [revert h1 Ln'k S1;clear;split;lia| | |];auto.
              cut (rebox k (sp_clean (t3 ⋅ t4)) =
                   (None,π2 (rebox k (sp_clean (t3 ⋅ t4))),None));
                [intros EE;repeat split|].
              repeat split.
              ** f_equal;f_equal;f_equal;f_equal;f_equal;f_equal.
                 rewrite H1;symmetry;apply IHK;repeat split;auto.
                 revert h1 Ln'k S1;clear;lia.
              ** rewrite EE in H2;revert H2 SR1 SR2.
                 rewrite <- En'.
                 clear.
                 repeat rewrite <- (sp_size_proper (sp_clean_eq _)).
                 generalize  (rebox k (sp_clean (t3 ⋅ t4))).
                 intro t;simpl.
                 destruct t1,t6;rsimpl;lia.
              ** revert L.
                 rewrite <- BR1,<-BR2.
                 unfold T_bind.
                 destruct t1,t6;simpl;
                   intros ->;f_equal;unfold prod,SeqBind;f_equal;clear;lia.
              ** revert G1 G2;clear;destruct t1,t6;simpl;tauto.
              ** rewrite <-BR1,<-BR2 in L.
                 cut (sp_bind (sp_clean (t3 ⋅ t4)) = 𝒷).
                 --- rewrite <- H3.
                     destruct (rebox k (sp_clean (t3 ⋅ t4)))
                       as (([]&?)&[]);simpl;intro E;inversion E;reflexivity.
                 --- revert L G1 G2.
                     assert (N : sp_bind (t3⋅t4) <> ℯ)
                       by (rewrite (sp_bind_proper (sp_clean_eq _)),
                           sp_binding_unit,<-sp_size_unit;
                           apply is_sp_clean_sp_size in C;revert C;clear;lia).
                     rewrite <- (sp_bind_proper (sp_clean_eq _)).
                     revert N;simpl;clear;intro N.
                     destruct t1,t6;simpl.
                     +++ intros E;inversion E.
                         destruct (sp_bind t3) as [| |];try tauto.
                         *** destruct (sp_bind t4) as [| |];try tauto.
                             simpl in H0;subst;simpl.
                             intros _ (_&_&->&_);reflexivity.
                         *** destruct (sp_bind t4) as [| |];try tauto.
                             ---- simpl in *;subst.
                                  intros (_&_&_&->);reflexivity.
                             ---- simpl in *.
                                  intros (_&_&_&->) (_&_&->&_);subst.
                                  unfold prod,SeqBind;f_equal;lia.
                     +++ intros E;inversion E.
                         destruct (sp_bind t3) as [| |];try tauto.
                         *** destruct (sp_bind t4) as [| |];try tauto.
                             simpl in H0;subst;simpl.
                             intros _ (_&->);reflexivity.
                         *** destruct (sp_bind t4) as [| |];try tauto.
                             ---- simpl in *;subst.
                                  intros (_&_&_&->);reflexivity.
                             ---- simpl in *.
                                  intros (_&_&_&->) (_&->);subst.
                                  unfold prod,SeqBind;f_equal;lia.
                     +++ intros E;inversion E.
                         destruct (sp_bind t3) as [| |];try tauto.
                         *** destruct (sp_bind t4) as [| |];try tauto.
                             simpl in H0;subst;simpl.
                             intros _ (_&_&->&_);reflexivity.
                         *** destruct (sp_bind t4) as [| |];try tauto.
                             ---- simpl in *;subst.
                                  intros (_&->);reflexivity.
                             ---- simpl in *.
                                  intros (_&->) (_&_&->&_);subst.
                                  unfold prod,SeqBind;f_equal;lia.
                     +++ intros E;inversion E.
                         destruct (sp_bind t3) as [| |];try tauto.
                         *** destruct (sp_bind t4) as [| |];try tauto.
                             simpl in H0;subst;simpl.
                             intros _ (_&->);reflexivity.
                         *** destruct (sp_bind t4) as [| |];try tauto.
                             ---- simpl in *;subst.
                                  intros (_&->);reflexivity.
                             ---- simpl in *.
                                  intros (_&->) (_&->);subst.
                                  unfold prod,SeqBind;f_equal;lia.
        -- repeat split.
           ++ simpl in En';rewrite <- En',<-SR1,<-SR2.
              simpl;destruct t1,t6;rsimpl;clear;lia.
           ++ rewrite <- BR1,<-BR2.
              simpl;destruct t1,t6;unfold prod,SeqBind;f_equal;clear;lia.
           ++ revert G1 G2;destruct t1,t6;simpl;clear;tauto.
    - simpl in h__bind.
      destruct h__clean as (h__clean1&h__clean2).
      destruct (@sp_bind_par_not_nil _ s1 s2 ℯ) as (E1&E2);
        try rewrite right_unit;try assumption.
      destruct (IHK k s1) as (R1&S1&B1);[| | |destruct (IHK k s2) as (R2&S2&B2)].
      + apply is_sp_clean_sp_size in h__clean2;simpl in *;lia.
      + assumption.
      + rewrite E1;discriminate.
      + apply is_sp_clean_sp_size in h__clean1;simpl in *;lia.
      + assumption.
      + rewrite E2;discriminate.
      + rewrite E1 in B1;rewrite E2 in B2.
        repeat split.
        * simpl.
          rewrite R1,R2.
          f_equal;f_equal;f_equal;f_equal;symmetry;apply IHK;auto.
          -- apply is_sp_clean_sp_size in h__clean2;simpl in *;lia.
          -- rewrite E1;discriminate.
          -- apply is_sp_clean_sp_size in h__clean1;simpl in *;lia.
          -- rewrite E2;discriminate.
        * simpl;rewrite <- En';simpl;rewrite <- S1,<-S2;clear.
          apply Plus.plus_le_compat.
          -- destruct (rebox k s1) as (([]&?)&[]);unfold π2;rsimpl;lia.
          -- destruct (rebox k s2) as (([]&?)&[]);unfold π2;rsimpl;lia.
        * simpl;rewrite E1,E2;reflexivity.
    - simpl;repeat split;reflexivity||lia.
    - simpl;repeat split;try reflexivity.
      + clear;lia.
      + discriminate.
    - simpl;repeat split;try reflexivity.
      + clear;lia.
      + discriminate.
    - exfalso;apply h__clean.    
  Qed.


  Definition Rebox s := (rebox ⎢s⎥ (sp_clean s)).

  Definition unpackT : T -> sp_terms X' :=
    fun t =>
      match t with
      | (None,t,None) => unbox t
      | (Some t1,t,None) => t1 ⋅ VClose ⋅ unbox t
      | (None,t,Some t2) => unbox t ⋅ VOpen ⋅ t2
      | (Some t1,t,Some t2) => t1 ⋅ VClose ⋅ unbox t ⋅ VOpen ⋅ t2
      end.

  Lemma unpackT_Rebox s : sp_bind s <> ↯ -> unpackT (Rebox s) ≡ s.
  Proof.
    unfold Rebox.
    rewrite (sp_bind_proper (sp_clean_eq s)).
    destruct (sp_clean_is_sp_clean s) as [E|C];
      [destruct ⎢s⎥;simpl;[|rewrite E;simpl];
       intros _;rsimpl in *;rewrite <- E;symmetry;apply sp_clean_eq|].
    rewrite (sp_size_proper (sp_clean_eq s)).
    rewrite (sp_clean_eq s) at 4.
    remember ⎢sp_clean s⎥ as k;
      assert (L:⎢sp_clean s⎥ <= k) by lia;
      clear Heqk;generalize dependent (sp_clean s);clear s;
        induction k;[intros s C;apply is_sp_clean_sp_size in C;lia|].
    intros s C L B.
    simpl.
    destruct s as [s t|s t|[x|[]]|].
    - unfold prod_T.
      pose proof C as (C1&C2).
      simpl in B;rewrite bind_error_seq in B.
      destruct (@rebox_invariants k s) as (S1&S2&S3&S4);
        [apply is_sp_clean_sp_size in C2;rsimpl in *;lia
        | assumption
        | revert B;tauto | ].
      destruct (@rebox_invariants k t) as (T1&T2&T3&T4);
        [apply is_sp_clean_sp_size in C1;rsimpl in *;lia
        | assumption
        | revert B;tauto | ].
      destruct (@cases_seq_prod (rebox k s) (rebox k t))
        as [(Hyp&D)|[(Hyp&D)|(Hyp&D)]];
        (rewrite S3||rewrite T3;revert B;tauto)||auto;
        rewrite S3,T3 in Hyp.
      + pose proof Hyp as l;apply Nat.ltb_lt in l as ->;simpl.
        rewrite <- (IHk t) at 2
          by (apply is_sp_clean_sp_size in C1;rsimpl in *;lia||assumption||tauto).
        destruct (rebox k t) as (([t1|]&t')&t2);
          [clear D|exfalso;destruct D as (?&?);discriminate].
        destruct t2;simpl;repeat rewrite (mon_assoc _);reflexivity.
      + pose proof Hyp as l;apply Nat.ltb_lt in l as ->;simpl.
        pose proof Hyp as l;apply Nat.lt_asymm,Nat.ltb_nlt in l as ->;simpl.
        simpl.
        rewrite <- (IHk s) at 2
          by (apply is_sp_clean_sp_size in C2;rsimpl in *;lia||assumption||tauto).
        destruct (rebox k s) as ((s1&s')&[s2|]);
          [clear D|exfalso;destruct D as (?&?);discriminate].
        destruct s1;simpl;repeat rewrite (mon_assoc _);reflexivity.
      + rewrite Hyp,Nat.ltb_irrefl.
        rewrite <- (IHk s) at 2
          by (apply is_sp_clean_sp_size in C2;rsimpl in *;lia||assumption||tauto).
        rewrite <- (IHk t)
          by (apply is_sp_clean_sp_size in C1;rsimpl in *;lia||assumption||tauto).
        destruct (rebox k s) as ((s1&s')&[s2|]),
                                (rebox k t) as (([t1|]&t')&t2);
          try (exfalso;destruct D as [(?&?&?&?)|(?&?)];discriminate);clear D.
        * remember (sp_clean (s2 ⋅ t1)) as 𝓈.
          cut (unbox (π2(rebox k 𝓈))≡𝓈).
          -- intros EE.
             simpl;destruct s1,t2.
             ++ repeat rewrite (mon_assoc _);
                  repeat (apply sp_eq_seq;[|reflexivity]).
                repeat rewrite <-(mon_assoc _);
                  repeat (apply sp_eq_seq;[reflexivity|]).
                rewrite EE;subst;symmetry;apply sp_clean_eq.
             ++ repeat rewrite (mon_assoc _);
                  repeat (apply sp_eq_seq;[|reflexivity]).
                repeat rewrite <-(mon_assoc _);
                  repeat (apply sp_eq_seq;[reflexivity|]).
                rewrite EE;subst;symmetry;apply sp_clean_eq.
             ++ repeat rewrite (mon_assoc _);
                  repeat (apply sp_eq_seq;[|reflexivity]).
                repeat rewrite <-(mon_assoc _);
                  repeat (apply sp_eq_seq;[reflexivity|]).
                rewrite EE;subst;symmetry;apply sp_clean_eq.
             ++ repeat rewrite (mon_assoc _);
                  repeat (apply sp_eq_seq;[|reflexivity]).
                repeat rewrite <-(mon_assoc _);
                  repeat (apply sp_eq_seq;[reflexivity|]).
                rewrite EE;subst;symmetry;apply sp_clean_eq.
          -- cut ((is_sp_clean 𝓈 /\ ⎢𝓈⎥ <= k /\ sp_bind 𝓈 <> ↯)\/ 𝓈 = 𝟭);
               [intros [hyps| ->]|].
             ++ destruct (@rebox_invariants k 𝓈) as (h1&h2&h3&h4);try tauto.
                etransitivity;[|apply IHk;tauto].
                destruct (rebox k 𝓈) as (([k1|]&ss)&[k2|]).
                ** exfalso.
                   simpl in h3,T3,S3.
                   rewrite Heq𝓈,<-(sp_bind_proper (sp_clean_eq _)) in h3.
                   simpl in h3.
                   rewrite <- T3, <- S3 in Hyp.
                   assert (EE: close (sp_bind t1) = open (sp_bind s2))
                     by (revert Hyp;destruct t2,s1;simpl;clear;intros E;inversion E;auto).
                   clear Hyp T1 T2 T3 S1 S2 S3 C1 C2 B.
                   assert (sp_bind s2 <> ↯ /\ close (sp_bind s2) = 0)
                     as (_&g6)
                     by (revert S4;clear;destruct s1;simpl;tauto);clear S4.
                   assert (sp_bind t1 <> ↯ /\ open (sp_bind t1) = 0)
                     as (_&g8)
                       by (revert T4;clear;destruct t2;simpl;tauto);clear T4.
                   revert g6 g8 EE h3;clear;intros.
                   destruct (sp_bind s2),(sp_bind t1);try (simpl in *;subst;discriminate).
                   simpl in g6,g8,EE;subst.
                   unfold prod,SeqBind;inversion h3;lia.
                ** exfalso.
                   simpl in h3,T3,S3.
                   rewrite Heq𝓈,<-(sp_bind_proper (sp_clean_eq _)) in h3.
                   simpl in h3.
                   rewrite <- T3, <- S3 in Hyp.
                   assert (EE: close (sp_bind t1) = open (sp_bind s2))
                     by (revert Hyp;destruct t2,s1;simpl;clear;intros E;inversion E;auto).
                   clear Hyp T1 T2 T3 S1 S2 S3 C1 C2 B.
                   assert (sp_bind s2 <> ↯ /\ close (sp_bind s2) = 0)
                     as (_&g6)
                     by (revert S4;clear;destruct s1;simpl;tauto);clear S4.
                   assert (sp_bind t1 <> ↯ /\ open (sp_bind t1) = 0)
                     as (_&g8)
                       by (revert T4;clear;destruct t2;simpl;tauto);clear T4.
                   revert g6 g8 EE h3;clear;intros.
                   destruct (sp_bind s2),(sp_bind t1);try (simpl in *;subst;discriminate).
                   simpl in g6,g8,EE;subst.
                   unfold prod,SeqBind;inversion h3;lia.
                ** exfalso.
                   simpl in h3,T3,S3.
                   rewrite Heq𝓈,<-(sp_bind_proper (sp_clean_eq _)) in h3.
                   simpl in h3.
                   rewrite <- T3, <- S3 in Hyp.
                   assert (EE: close (sp_bind t1) = open (sp_bind s2))
                     by (revert Hyp;destruct t2,s1;simpl;clear;intros E;inversion E;auto).
                   clear Hyp T1 T2 T3 S1 S2 S3 C1 C2 B.
                   assert (sp_bind s2 <> ↯ /\ close (sp_bind s2) = 0)
                     as (_&g6)
                     by (revert S4;clear;destruct s1;simpl;tauto);clear S4.
                   assert (sp_bind t1 <> ↯ /\ open (sp_bind t1) = 0)
                     as (_&g8)
                       by (revert T4;clear;destruct t2;simpl;tauto);clear T4.
                   revert g6 g8 EE h3;clear;intros.
                   destruct (sp_bind s2),(sp_bind t1);try (simpl in *;subst;discriminate).
                   simpl in g6,g8,EE;subst.
                   unfold prod,SeqBind;inversion h3;lia.
                ** reflexivity.
             ++ destruct k;reflexivity.
             ++ subst;destruct (sp_clean_is_sp_clean (s2⋅t1)) as [-> | C'];
                  [now right|left].
                split;[assumption|].
                rewrite <- (sp_bind_proper (sp_clean_eq _)),
                <- (sp_size_proper (sp_clean_eq _)).
                simpl;rewrite bind_error_seq.
                split.
                ** cut (⎢s2⎥ < ⎢s⎥ /\ ⎢t1⎥ < ⎢t⎥).
                   --- apply is_sp_clean_sp_size in C1.
                       apply is_sp_clean_sp_size in C2.
                       revert L;rsimpl;clear.
                       lia.
                   --- split.
                       +++ revert S2;clear;rsimpl;destruct s1;rsimpl;lia.
                       +++ revert T2;clear;rsimpl;destruct t2;rsimpl;lia.
                ** revert S4 T4;clear;destruct s1,t2;simpl;tauto.
        * simpl;destruct s1,t2;simpl;repeat rewrite (mon_assoc _);reflexivity.
    - simpl.
      pose proof C as (C1&C2).
      destruct (@sp_bind_par_not_nil _ s t ℯ) as (Bs&Bt);auto;
        [rewrite right_unit;apply B|].
      destruct (@rebox_invariants k s) as (S1&S2&S3&S4);
        [apply is_sp_clean_sp_size in C2;rsimpl in *;lia
        | assumption
        | rewrite Bs;discriminate | ].
      destruct (@rebox_invariants k t) as (T1&T2&T3&T4);
        [apply is_sp_clean_sp_size in C1;rsimpl in *;lia
        | assumption
        | rewrite Bt;discriminate | ].
      apply sp_eq_par;(etransitivity;[|apply IHk]);
        try assumption
        ||(apply is_sp_clean_sp_size in C1;
          apply is_sp_clean_sp_size in C2;rsimpl in *;lia)
        ||(rewrite Bs||rewrite Bt;discriminate).
      + destruct (rebox k s) as (([]&s')&[]);try reflexivity.
        * exfalso;rewrite Bs in S3;revert S3;discriminate.
        * exfalso;rewrite Bs in S3;revert S3;discriminate.
        * exfalso;rewrite Bs in S3;revert S3;discriminate.
      + destruct (rebox k t) as (([]&t')&[]);try reflexivity.
        * exfalso;rewrite Bt in T3;revert T3;discriminate.
        * exfalso;rewrite Bt in T3;revert T3;discriminate.
        * exfalso;rewrite Bt in T3;revert T3;discriminate.
    - reflexivity.
    - simpl;rewrite left_unit,right_unit;reflexivity.
    - simpl;rewrite left_unit,right_unit;reflexivity.
    - reflexivity.
  Qed.

  Lemma sp_clean_dec_prod (s t : sp_terms X') :
    (sp_clean s = 𝟭 /\ sp_clean t = 𝟭 /\ sp_clean (s⋅t) = 𝟭)
    \/  (sp_clean s = 𝟭 /\ is_sp_clean (sp_clean t) /\ sp_clean (s⋅t) = sp_clean t)
    \/  (is_sp_clean (sp_clean s) /\ sp_clean t = 𝟭 /\ sp_clean (s⋅t) = sp_clean s)
    \/  (is_sp_clean (sp_clean s) /\ is_sp_clean (sp_clean t)
        /\ sp_clean (s⋅t) = sp_clean s ⋅sp_clean t).
  Proof.
    simpl;destruct (sp_clean_is_sp_clean s) as [->|Cs];
      destruct (sp_clean_is_sp_clean t) as [->|Ct];simpl;auto.
    - right;right;left.
      split;[|split];auto.
      destruct (sp_clean s);auto.
    - repeat right.
      split;[|split];auto.
      destruct (sp_clean s),(sp_clean t);simpl in *;reflexivity||tauto.
  Qed.

  Lemma rebox_switch n m (s : sp_terms X'):
    sp_bind s <> ↯ -> ⎢s⎥ <= n -> ⎢s⎥ <= m ->
    rebox n (sp_clean s) = rebox m (sp_clean s).
  Proof.
    destruct (sp_clean_is_sp_clean s) as [->|C].
    - destruct n,m;reflexivity.
    - intros B S1 S2.
      rewrite (sp_bind_proper (sp_clean_eq _)) in B.
      rewrite (sp_size_proper (sp_clean_eq _)) in S1,S2.
      etransitivity;[|symmetry];apply rebox_invariants;auto.
  Qed.
  
  Lemma Rebox_equiv s t : s≡t -> sp_bind s <> ↯ -> Rebox s ≡ Rebox t.
  Proof.
    intros E B;unfold Rebox.
    remember ⎢s⎥ as k;rewrite <- (sp_size_proper E),<-Heqk.
    assert (hk : ⎢s⎥ <= k) by lia.
    clear Heqk;revert s t hk E B;induction k;[intros;reflexivity|].
    intros s t L E;induction E.
    - reflexivity.
    - intro S;symmetry;apply IHE.
      + rewrite (sp_size_proper H);assumption.
      + rewrite (sp_bind_proper H);assumption.
    - intros S;etransitivity;[apply IHE|apply IHE0].
      + assumption.
      + assumption.
      + rewrite <- (sp_size_proper H);assumption.
      + rewrite <- (sp_bind_proper H);assumption.
    - set (sk := S k).
      intros B;simpl in B.
      assert (sp_bind s <> ↯ /\ sp_bind s' <> ↯ /\ ⎢s⎥ <= S k /\ ⎢s'⎥ <= S k)
        as (Bs&Bs'&Ss&Ss')
          by (rewrite bind_error_seq in B;repeat split;rsimpl in *;
              (simpl in L;lia)||(intros EE;rewrite EE in B;tauto));clear B.
      assert (sp_bind t <> ↯ /\ sp_bind t' <> ↯) as (Bt&Bt')
          by (rewrite <- (sp_bind_proper H), <-(sp_bind_proper H0);
              tauto).
      pose proof (IHE Ss Bs) as ih;pose proof (IHE0 Ss' Bs') as ih';clear IHE IHE0.
      unfold Rebox.
      destruct (sp_clean_dec_prod s s') as
          [(Es&Es'&->)|[(Es&Cs'&->)|[(Cs&Es'&->)|(Cs&Cs'&->)]]].
      + replace (sp_clean (t ⋅ t')) with (@sp_unit X').
        * reflexivity.
        * symmetry;destruct (sp_clean_is_sp_clean (t⋅t')) as [->|F];[reflexivity|].
          exfalso.
          apply is_sp_clean_sp_size in F.
          rewrite <- (sp_size_proper(sp_clean_eq _)) in F.
          rsimpl in F.
          rewrite <- (sp_size_proper H),(sp_size_proper(sp_clean_eq s)),Es in F.
          rewrite <- (sp_size_proper H0),(sp_size_proper(sp_clean_eq s')),Es' in F.
          rsimpl in F;lia.
      + replace (sp_clean (t ⋅ t')) with (sp_clean t');auto.
        destruct (sp_clean_is_sp_clean t) as [Et|Ct].
        * simpl;rewrite Et;reflexivity.
        * exfalso.
          rewrite (sp_clean_eq s),(sp_clean_eq t) in H.
          apply sp_size_proper in H.
          rewrite Es in H.
          apply is_sp_clean_sp_size in Ct;rsimpl in H;lia.
      + replace (sp_clean (t ⋅ t')) with (sp_clean t);auto.
        destruct (sp_clean_is_sp_clean t') as [Et|Ct].
        * simpl;rewrite Et;simpl;destruct (sp_clean t);reflexivity.
        * exfalso.
          rewrite (sp_clean_eq s'),(sp_clean_eq t') in H0.
          apply sp_size_proper in H0.
          rewrite Es' in H0.
          apply is_sp_clean_sp_size in Ct;rsimpl in H0;lia.
      + rewrite sp_clean_seq_clean;
          [
          | destruct (sp_clean_is_sp_clean t) as [E|E]; [|assumption ];
            apply is_sp_clean_sp_size in Cs;
            rewrite (sp_clean_eq s),(sp_clean_eq t) in H;
            rewrite (sp_size_proper H) in Cs;
            rewrite E in *;rsimpl in *;lia
          | destruct (sp_clean_is_sp_clean t') as [E|E]; [|assumption ];
            apply is_sp_clean_sp_size in Cs';
            rewrite (sp_clean_eq s'),(sp_clean_eq t') in H0;
            rewrite (sp_size_proper H0) in Cs';
            rewrite E in *;rsimpl in *;lia].
        unfold sk;simpl.
        cut (⎢s⎥ <= k /\ ⎢s'⎥ <= k);
          [|rsimpl in L;
            apply is_sp_clean_sp_size in Cs;apply is_sp_clean_sp_size in Cs';
            rewrite <- (sp_size_proper(sp_clean_eq _)) in Cs;
            rewrite <-(sp_size_proper(sp_clean_eq _)) in Cs';lia].
        intros (S1&S2).
        rewrite <- (rebox_switch Bs S1 Ss) in ih.
        rewrite <- (rebox_switch Bs' S2 Ss') in ih'.
        rewrite <- (@rebox_switch k _ _ Bt) in ih
          by (reflexivity||apply sp_size_proper in H;lia).
        rewrite <- (@rebox_switch k _ _ Bt') in ih'
          by (reflexivity||apply sp_size_proper in H0;lia).
        rewrite (sp_size_proper (sp_clean_eq s)) in S1.
        rewrite (sp_size_proper (sp_clean_eq s')) in S2.
        rewrite (sp_bind_proper (sp_clean_eq s)) in Bs.
        rewrite (sp_bind_proper (sp_clean_eq s')) in Bs'.
        rewrite (sp_bind_proper (sp_clean_eq t)) in Bt.
        rewrite (sp_bind_proper (sp_clean_eq t')) in Bt'.
        rewrite (sp_clean_eq s),(sp_clean_eq t) in H.
        rewrite (sp_clean_eq s'),(sp_clean_eq t') in H0.
        rsimpl in L.
        rewrite (sp_size_proper (sp_clean_eq s)) in L.
        rewrite (sp_size_proper (sp_clean_eq s')) in L.
        clear Ss Ss'.
        generalize dependent (sp_clean t');
        generalize dependent (sp_clean t);
        generalize dependent (sp_clean s');
        generalize dependent (sp_clean s);clear s t s' t'.
        intros s Bs Cs Ss s' h__size Bs' Cs' Ss' t Et Bt ih t' Et' Bt' ih'.
        destruct (@rebox_invariants k s) as (_&R2&R3&R4);auto.
        destruct (@rebox_invariants k s') as (_&R'2&R'3&R'4);auto.
        destruct (@cases_seq_prod (rebox k s) (rebox k s')) as [(L&E)|[(L&E)|(L&E)]];auto;
          try rewrite R3,R'3 in L.
        * rewrite R3;auto.
        * rewrite R'3;auto.
        * unfold prod_T;pose proof L as l;apply Nat.ltb_lt in l as -> ;
            pose proof L as l;rewrite (sp_bind_proper Et),(sp_bind_proper Et') in l;
              apply Nat.ltb_lt in l as -> .
          destruct (rebox k s') as ((S1&S2)&S3), (rebox k t') as ((T1&T2)&T3).
          destruct S1;[|destruct E as (?&E);exfalso;revert E;discriminate].
          destruct ih' as (ih1&ih2&ih3);
            unfold π1,π2,π3 in ih1,ih2,ih3;simpl in ih1,ih2,ih3.
          destruct T1;[|exfalso;apply ih1].
          repeat split;unfold π1,π2,π3;simpl;auto.
          unfold equiv,equiv_opt.
          unfold equiv,equiv_opt in ih1.
          rewrite ih1,Et;reflexivity.
        * unfold prod_T;pose proof L as l;apply Nat.ltb_lt in l as -> ;
            pose proof L as l;rewrite (sp_bind_proper Et),(sp_bind_proper Et') in l;
              apply Nat.ltb_lt in l as -> .
          pose proof L as l;apply Nat.lt_asymm,Nat.ltb_nlt in l as -> ;
            pose proof L as l;rewrite (sp_bind_proper Et),(sp_bind_proper Et') in l;
              apply Nat.lt_asymm,Nat.ltb_nlt in l as -> .
          destruct (rebox k s) as ((S1&S2)&S3), (rebox k t) as ((T1&T2)&T3).
          destruct S3;[|destruct E as (?&E);exfalso;revert E;discriminate].
          destruct ih as (ih1&ih2&ih3);
            unfold π1,π2,π3 in ih1,ih2,ih3;simpl in ih1,ih2,ih3.
          destruct T3;[|exfalso;apply ih3].
          repeat split;unfold π1,π2,π3;simpl;auto.
          unfold equiv,equiv_opt.
          unfold equiv,equiv_opt in ih3.
          rewrite ih3,Et';reflexivity.
        * unfold prod_T.
          rewrite <- (sp_bind_proper Et),<-(sp_bind_proper Et'),L,Nat.ltb_irrefl.
          destruct (rebox k s) as ((S1&S2)&S3), (rebox k t) as ((T1&T2)&T3).
          destruct (rebox k s') as ((S'1&S'2)&S'3), (rebox k t') as ((T'1&T'2)&T'3).
          destruct ih as (ih1&ih2&ih3),ih' as (ih'1&ih'2&ih'3).
          unfold π3,π2,π1 in E,ih1,ih2,ih3,ih'1,ih'2,ih'3;
            simpl in E,ih1,ih2,ih3,ih'1,ih'2,ih'3.
          destruct E as [(s3&s'1&->&->)|(->&->)].
          -- destruct T3 as [t3|];[|exfalso;apply ih3].
             destruct T'1 as [t'1|];[|exfalso;apply ih'1].
             repeat split;unfold π1,π3;try assumption.
             unfold π2 at 1 3.
             apply bsp_eq_seq;[|assumption].
             apply bsp_eq_seq;[assumption|].
             apply bsp_eq_box.
             cut (rebox k (sp_clean (s3 ⋅ s'1)) ≡ rebox k (sp_clean (t3 ⋅ t'1)));
               [intros (_&E&_);apply E|].
             cut (s3⋅s'1≡t3⋅t'1);[|apply sp_eq_seq;[apply ih3|apply ih'1]].
             intros hyp;apply IHk.
             ++ revert R2 R'2 h__size;rsimpl.
                destruct S1, S'3;clear;rsimpl;lia.
             ++ assumption.
             ++ revert R4 R'4;simpl;rewrite bind_error_seq.
                destruct S1, S'3;clear;tauto.
          -- destruct T3 as [t3|];[exfalso;apply ih3|].
             destruct T'1 as [t'1|];[exfalso;apply ih'1|].
             repeat split;unfold π1,π2,π3;simpl;auto.
    - set (sk := S k).
      intros B;simpl in B.
      assert (sp_bind s <> ↯ /\ sp_bind s' <> ↯ /\ ⎢s⎥ <= S k /\ ⎢s'⎥ <= S k)
        as (Bs&Bs'&Ss&Ss')
          by (apply bind_error_par in B;repeat split;rsimpl in *;
              (simpl in L;lia)||(intros EE;rewrite EE in B;tauto));clear B.
      assert (sp_bind t <> ↯ /\ sp_bind t' <> ↯) as (Bt&Bt')
          by (rewrite <- (sp_bind_proper H), <-(sp_bind_proper H0);
              tauto).
      pose proof (IHE Ss Bs) as ih;pose proof (IHE0 Ss' Bs') as ih';clear IHE IHE0.
      destruct (sp_clean_dec_par s s') as
          [(Es&Es'&->)|[(Es&Cs'&->)|[(Cs&Es'&->)|(Cs&Cs'&->)]]].
      + replace (sp_clean (t ∥ t')) with (@sp_unit X').
        * reflexivity.
        * symmetry;destruct (sp_clean_is_sp_clean (t∥t')) as [->|F];[reflexivity|].
          exfalso.
          apply is_sp_clean_sp_size in F.
          rewrite <- (sp_size_proper(sp_clean_eq _)) in F.
          rsimpl in F.
          rewrite <- (sp_size_proper H),(sp_size_proper(sp_clean_eq s)),Es in F.
          rewrite <- (sp_size_proper H0),(sp_size_proper(sp_clean_eq s')),Es' in F.
          rsimpl in F;lia.
      + replace (sp_clean (t ∥ t')) with (sp_clean t');auto.
        destruct (sp_clean_is_sp_clean t) as [Et|Ct].
        * simpl;rewrite Et;reflexivity.
        * exfalso.
          rewrite (sp_clean_eq s),(sp_clean_eq t) in H.
          apply sp_size_proper in H.
          rewrite Es in H.
          apply is_sp_clean_sp_size in Ct;rsimpl in H;lia.
      + replace (sp_clean (t ∥ t')) with (sp_clean t);auto.
        destruct (sp_clean_is_sp_clean t') as [Et|Ct].
        * simpl;rewrite Et;simpl;destruct (sp_clean t);reflexivity.
        * exfalso.
          rewrite (sp_clean_eq s'),(sp_clean_eq t') in H0.
          apply sp_size_proper in H0.
          rewrite Es' in H0.
          apply is_sp_clean_sp_size in Ct;rsimpl in H0;lia.
      + replace (sp_clean (t ∥ t')) with (sp_clean t ∥ sp_clean t').
        * unfold sk;simpl.
          split;[reflexivity|split;[|reflexivity]].
          apply bsp_eq_par.
          -- simpl in L.
             repeat rewrite (@rebox_switch k (S k)).
             ++ apply ih.
             ++ assumption.
             ++ rewrite <- (sp_size_proper H) in *.
                apply is_sp_clean_sp_size in Cs'.
                rewrite <- (sp_size_proper (sp_clean_eq _)) in Cs'.
                rsimpl in *;lia.
             ++ rewrite <- (sp_size_proper H) in *;assumption.
             ++ assumption.
             ++ apply is_sp_clean_sp_size in Cs'.
                rewrite <- (sp_size_proper (sp_clean_eq _)) in Cs'.
                rsimpl in *;lia.
             ++ assumption.
          -- simpl in L.
             repeat rewrite (@rebox_switch k (S k)).
             ++ apply ih'.
             ++ assumption.
             ++ rewrite <- (sp_size_proper H0) in *.
                apply is_sp_clean_sp_size in Cs.
                rewrite <- (sp_size_proper (sp_clean_eq _)) in Cs.
                rsimpl in *;lia.
             ++ rewrite <- (sp_size_proper H0) in *;assumption.
             ++ assumption.
             ++ apply is_sp_clean_sp_size in Cs.
                rewrite <- (sp_size_proper (sp_clean_eq _)) in Cs.
                rsimpl in *;lia.
             ++ assumption.
        * destruct (sp_clean_is_sp_clean t) as [Et|Ct];
            [|destruct (sp_clean_is_sp_clean t') as [Et'|Ct']].
          -- rewrite (sp_clean_eq s),(sp_clean_eq t),Et in H.
             apply sp_size_proper in H.
             apply is_sp_clean_sp_size in Cs.
             rsimpl in H;lia.
          -- rewrite (sp_clean_eq s'),(sp_clean_eq t'),Et' in H0.
             apply sp_size_proper in H0.
             apply is_sp_clean_sp_size in Cs'.
             rsimpl in H0;lia.
          -- simpl;destruct (sp_clean t),(sp_clean t');
               reflexivity||(simpl in Ct,Ct';tauto).
    - intros B;simpl in B.
      set (sk := S k).
      revert L;intro h__size;simpl in h__size.
      destruct (sp_clean_dec_prod s t) as
          [(Es&Et&E1) | [ (Es&Et&E1) |  [ (Es&Et&E1) | (Es&Et&E1) ] ] ] ;
        destruct (sp_clean_dec_prod t u)
        as [(Et'&Eu&E2)|[(Et'&Eu&E2)|[(Et'&Eu&E2)|(Et'&Eu&E2)]]];
        try (exfalso;(rewrite Et' in Et;revert Et;clear;simpl; tauto)
                     ||(rewrite Et in Et';revert Et';clear;simpl;tauto));
        repeat (rewrite sp_clean_seq_left by
                   (try rewrite E1||rewrite E2;assumption||reflexivity))
        || (rewrite sp_clean_seq_right by
              (try rewrite E1||rewrite E2;assumption||reflexivity))
        || (rewrite sp_clean_seq_clean by
              (try rewrite E1||rewrite E2;simpl in *;tauto));
        simpl;try reflexivity.
      cut (sp_bind s <> ↯ /\ sp_bind t <> ↯ /\ sp_bind u <> ↯);
        [clear B;intros (Bs&Bt&Bu)|repeat rewrite bind_error_seq in B;tauto].
      clear E1 E2 Et'.
      rsimpl in h__size.
      rewrite (sp_size_proper(sp_clean_eq s)),
      (sp_size_proper(sp_clean_eq t)),
      (sp_size_proper(sp_clean_eq u)) in h__size.
      rewrite (sp_bind_proper(sp_clean_eq _)) in Bs;
        rewrite (sp_bind_proper(sp_clean_eq _)) in Bt;
        rewrite (sp_bind_proper(sp_clean_eq _)) in Bu.
      assert ( 0 < ⎢sp_clean s⎥ < k
               /\ 0 < ⎢sp_clean t⎥ < k
               /\ 0 < ⎢sp_clean u⎥ < k) as (Ss&St&Su)
          by (apply is_sp_clean_sp_size in Es;
              apply is_sp_clean_sp_size in Et;
              apply is_sp_clean_sp_size in Eu;
              lia).
      generalize dependent (sp_clean u);
        generalize dependent (sp_clean t);
        generalize dependent (sp_clean s);clear s t u.
      intros s Cs Bs Ss t Ct Bt St u h__size Cu Bu Su.
      simpl.
      destruct (@rebox_invariants k s) as (_&hs1&hs2&hs3);try (auto;lia).
      destruct (@rebox_invariants k t) as (_&ht1&ht2&ht3);try (auto;lia).
      destruct (@rebox_invariants k u) as (_&hu1&hu2&hu3);try (auto;lia).
      destruct (@rebox_invariants k (t⋅u)) as (_&htu1&htu2&htu3);
        [rsimpl;lia|simpl;tauto|rsimpl;rewrite bind_error_seq;tauto|].
      destruct (@rebox_invariants k (s⋅t)) as (_&hst1&hst2&hst3);
        [rsimpl;lia|simpl;tauto|rsimpl;rewrite bind_error_seq;tauto|].
      destruct (@cases_seq_prod (rebox k s) (rebox k (t⋅u)))
        as [(L1&E1)|[(L1&E1)|(L1&E1)]];
        try rewrite hs2 in *;try rewrite htu2 in *;
          [assumption |simpl;rewrite bind_error_seq;tauto|assumption|assumption| | |].
      + unfold prod_T at 1.
        pose proof L1 as l;apply Nat.ltb_lt in l as ->.
        remember (rebox k (t⋅u)) as TU;destruct TU as (([TU1|]&TU2)&TU3);
          [clear E1|exfalso;revert E1;clear;intros (?&?);discriminate].
        destruct (@cases_seq_prod (rebox k (s⋅t)) (rebox k u))
          as [(L2&E2)|[(L2&E2)|(L2&E2)]];
          try rewrite hu2 in *;try rewrite hst2 in *;
            [simpl;rewrite bind_error_seq;tauto|assumption |assumption|assumption| | |].
        * unfold prod_T.
          pose proof L2 as l;apply Nat.ltb_lt in l as ->.
          destruct (@cases_seq_prod (rebox k t) (rebox k u))
            as [(L3&E3)|[(L3&E3)|(L3&E3)]];
            try rewrite hu2 in *;try rewrite ht2 in *;auto;
              try (simpl in L1,L2,L3;
                   rewrite close_prod in L1 by (rewrite bind_error_seq;tauto);
                   rewrite open_prod in L2 by (rewrite bind_error_seq;tauto);lia).
          remember (rebox k u) as U;destruct U as (([U1|]&U2)&U3);
            [clear E2|exfalso;revert E2;clear;intros (?&?);discriminate];clear E3.
          revert HeqTU.
          destruct k;[exfalso;revert Su;clear;lia|].
          simpl;unfold prod_T.
          pose proof L3 as l ;apply Nat.ltb_lt in l as ->.
          rewrite <- (sp_clean_idem Cu), (@rebox_switch _ (S k)) by (lia||auto).
          rewrite (sp_clean_idem Cu), <- HeqU.
          intro E;inversion E;subst.
          repeat split;unfold π1,π2,π3;simpl;try reflexivity.
          apply sp_eq_seq_ass.
        * unfold prod_T.
          pose proof L2 as l;apply Nat.lt_asymm,Nat.ltb_nlt in l as ->.
          pose proof L2 as l;apply Nat.ltb_lt in l as ->.
          destruct (@cases_seq_prod (rebox k t) (rebox k u))
            as [(L3&E3)|[(L3&E3)|(L3&E3)]];
            try rewrite hu2 in *;try rewrite ht2 in *;auto;
              try (simpl in L1,L2,L3;
                   rewrite close_prod in L1 by (rewrite bind_error_seq;tauto);
                   rewrite open_prod in L2 by (rewrite bind_error_seq;tauto);lia).
          remember (rebox k (s⋅t)) as ST;destruct ST as ((ST1&ST2)&[ST3|]);
            [clear E2|exfalso;revert E2;clear;intros (?&?);discriminate];clear E3.
          revert HeqST.
          destruct k;[exfalso;revert Su;clear;lia|].
          assert (L4 : open (sp_bind s) < close (sp_bind t))
            by (revert decX Bs Bt Bu L1 L2 L3;clear;simpl;intros;
                rewrite close_prod in L1 by (rewrite bind_error_seq;tauto);
                rewrite open_prod in L2 by (rewrite bind_error_seq;tauto);lia).
          simpl;unfold prod_T.
          pose proof L4 as l ;apply Nat.ltb_lt in l as ->.
          remember (rebox k t) as T;destruct T as (([T1|]&T2)&T3);[|clear;discriminate].
          intros E;inversion E;subst;clear E.
          revert HeqTU.
          simpl;unfold prod_T.
          pose proof L3 as l ;apply Nat.ltb_lt in l as ->.
          pose proof L3 as l ;apply Nat.lt_asymm, Nat.ltb_nlt in l as ->.
          rewrite <- HeqT.
          intro E;inversion E;subst;clear E.
          repeat split;unfold π1,π2,π3;simpl;try reflexivity.
        * unfold prod_T;rewrite L2,Nat.ltb_irrefl.
          assert (L4 : open (sp_bind s) < close (sp_bind t))
            by (revert decX Bs Bt Bu L1 L2;clear;simpl;intros;
                rewrite close_prod in L1 by (rewrite bind_error_seq;tauto);
                rewrite open_prod in L2 by (rewrite bind_error_seq;tauto);lia).
          remember (rebox k (s⋅t)) as ST;destruct ST as ((ST1&ST2)&s').
          remember (rebox k u) as U;destruct U as ((u'&U2)&U3).
          unfold π3,π1 in E2;simpl in E2.
          destruct E2 as [(ST3&U1&->&->)|(->&->)].
          -- remember (rebox k (sp_clean (ST3 ⋅ U1))) as M;destruct M as ((M1&M2)&M3).
             unfold π2;simpl.
             revert HeqST HeqTU.
             destruct k;[exfalso;revert Su;clear;lia|];simpl.
             unfold prod_T at 1.
             pose proof L4 as l ;apply Nat.ltb_lt in l as ->.
             remember (rebox k t) as T;destruct T as (([T1|]&T2)&T3);
               [|discriminate].
             intros E;inversion E;subst;clear E.
             rewrite <- (sp_clean_idem Cs), <- (@rebox_switch k (S k)),(sp_clean_idem Cs)
               in hs1,hs2,hs3 by (revert Ss Bs;clear;lia||auto).
             rewrite <- (sp_clean_idem Ct), <- (@rebox_switch k (S k)),(sp_clean_idem Ct)
               in ht1,ht2,ht3 by (revert St Bt;clear;lia||auto).
             rewrite <- (sp_clean_idem Cu), <- (@rebox_switch k (S k)),(sp_clean_idem Cu)
               in HeqU by (revert Su Bu;clear;lia||auto).
             destruct (@cases_seq_prod (rebox k t)(Some U1, U2, U3))
               as [(L3&E3)|[(L3&E3)|(L3&E3)]];
               try rewrite hu2 in *;try rewrite ht2 in *;auto;
                 try (simpl in L1,L2,L3;
                      rewrite close_prod in L1 by (rewrite bind_error_seq;tauto);
                      rewrite open_prod in L2 by (rewrite bind_error_seq;tauto);lia).
             clear E3.
             unfold prod_T;rewrite L3,Nat.ltb_irrefl,<-HeqT,<-HeqU.
             rewrite (@rebox_switch k (S k)).
             ++ rewrite <- HeqM;unfold π2;simpl. 
                intro E;inversion E;subst;clear E.
                reflexivity.
             ++ simpl;rewrite bind_error_seq.
                revert hst3 hu3;destruct U3;simpl;clear;tauto.
             ++ revert hst1 hu1 h__size;simpl;destruct U3;clear;rsimpl;lia.
             ++ revert hst1 hu1 h__size;simpl;destruct U3;clear;rsimpl;lia.
          -- revert HeqST HeqTU.
             destruct k;[exfalso;revert Su;clear;lia|];simpl.
             unfold prod_T at 1.
             pose proof L4 as l ;apply Nat.ltb_lt in l as ->.
             remember (rebox k t) as T;destruct T as ((T1&T2)&T3).
             rewrite <- (sp_clean_idem Cs), <- (@rebox_switch k (S k)),(sp_clean_idem Cs)
               in hs1,hs2,hs3 by (revert Ss Bs;clear;lia||auto).
             rewrite <- (sp_clean_idem Ct), <- (@rebox_switch k (S k)),(sp_clean_idem Ct)
               in ht1,ht2,ht3 by (revert St Bt;clear;lia||auto).
             rewrite <- (sp_clean_idem Cu), <- (@rebox_switch k (S k)),(sp_clean_idem Cu)
               in HeqU by (revert Su Bu;clear;lia||auto).
             assert (EE : close (sp_bind u) = 0)
               by (rewrite <- hu2;simpl;destruct U3;simpl;reflexivity).
             simpl in L1,L2.
             rewrite close_prod in L1 by (rewrite bind_error_seq;tauto);
               rewrite open_prod in L2 by (rewrite bind_error_seq;tauto).
             rewrite EE in *.
             assert (EE' : open (sp_bind t) = 0) by (revert L2;lia).
             clear L2 L1.
             unfold prod_T;rewrite EE,EE',Nat.ltb_irrefl.
             rewrite <- HeqT,<-HeqU.
             destruct T1.
             ++ intro E;inversion E;subst;clear E.
                intro E;inversion E;subst;clear E.
                reflexivity.
             ++ intro E;inversion E;subst;clear E.
                destruct T3;discriminate.
      + assert (L2 : close (sp_bind u) < open (sp_bind (s ⋅ t)))
          by (revert decX Bs Bt Bu L1;clear;intros;revert L1;simpl;
              rewrite close_prod  by (rewrite bind_error_seq;tauto);
              rewrite open_prod by (rewrite bind_error_seq;tauto);
              lia).
        assert (L3 : close (sp_bind t) < open (sp_bind s))
          by (revert decX Bs Bt Bu L1;clear;intros;revert L1;simpl;
              rewrite close_prod  by (rewrite bind_error_seq;tauto);
              lia).
        unfold prod_T.
        pose proof L1 as l;apply Nat.ltb_lt in l as ->.
        pose proof L1 as l;apply Nat.lt_asymm,Nat.ltb_nlt in l as ->.
        pose proof L2 as l;apply Nat.ltb_lt in l as ->.
        pose proof L2 as l;apply Nat.lt_asymm,Nat.ltb_nlt in l as ->.
        remember (rebox k s) as S;destruct S as ((S1,S2)&[S3|]);
          [clear E1|exfalso;revert E1;clear;firstorder discriminate].
        destruct k as [|k];[exfalso;revert Su;lia|].
        simpl;unfold prod_T.
        pose proof L3 as l;apply Nat.ltb_lt in l as ->.
        pose proof L3 as l;apply Nat.lt_asymm,Nat.ltb_nlt in l as ->.
        rewrite <- (sp_clean_idem Cs), <- (@rebox_switch k (S k)),(sp_clean_idem Cs)
          in HeqS by (revert Ss Bs;clear;lia||auto).
        rewrite <- HeqS.
        repeat split;try reflexivity.
        apply sp_eq_seq_ass.
      + assert (L3 : close (sp_bind t) <= open (sp_bind s))
          by (revert decX Bs Bt Bu L1;clear;intros;revert L1;simpl;
              rewrite close_prod  by (rewrite bind_error_seq;tauto);
              lia).
        apply Compare_dec.le_lt_eq_dec in L3 as [L3|L3].
        * assert (L4 : open (sp_bind t) < close (sp_bind u))
          by (revert decX Bs Bt Bu L3 L1;clear;intros;revert L1;simpl;
              rewrite close_prod  by (rewrite bind_error_seq;tauto);
              lia).
          assert (L2 : close (sp_bind u) = open (sp_bind (s ⋅ t)))
            by (revert decX Bs Bt Bu L1 L3 L4;clear;intros ? ? ? ?;simpl;
                rewrite close_prod by (rewrite bind_error_seq;tauto);
                  rewrite open_prod by (rewrite bind_error_seq;tauto);lia).
          unfold prod_T;rewrite L1,Nat.ltb_irrefl,L2,Nat.ltb_irrefl.
          destruct k as [|k];[exfalso;revert Su;clear;lia|].
          remember (rebox k s) as S;destruct S as ((S1,S2)&s').
          remember (rebox (S k) (t⋅u)) as TU;destruct TU as ((tu',TU2)&TU3).
          remember (rebox k u) as U;destruct U as ((u',U2)&U3).
          remember (rebox k t) as T;destruct T as ((T1,T2)&T3).
          remember (rebox (S k) (s⋅t)) as ST;destruct ST as ((ST1,ST2)&ST3).
          replace (rebox (S k) s) with (rebox k s) in *
            by (rewrite <- (sp_clean_idem Cs), <- (@rebox_switch k (S k) s),
                (sp_clean_idem Cs)
                 by (revert Ss Bs;clear;lia||auto);reflexivity).
          replace (rebox (S k) u) with (rebox k u) in *
            by (rewrite <- (sp_clean_idem Cu), <- (@rebox_switch k (S k) u),
                (sp_clean_idem Cu)
                 by (revert Su Bu;clear;lia||auto);reflexivity).
          rewrite <- HeqS,<-HeqU in *.
          unfold π1,π3 in E1;simpl in E1.
          destruct E1 as [(S3&TU1&->&->)|(->&->)].
          -- remember (rebox (S k) (sp_clean (S3⋅TU1))) as M;destruct M as ((M1,M2),M3).
             assert (ST1 = S1 /\ ST2 = S2 /\ ST3 = Some (S3 ⋅ t)
                     /\ (exists U1, u' = Some U1 /\ TU1 = t ⋅ U1)
                     /\ TU2 = U2 /\ TU3 = U3)
               as (->&->&->&(U1&->&->)&->&->).
             ++ revert HeqST HeqTU.
                simpl;unfold prod_T.
                pose proof L3 as l;apply Nat.ltb_lt in l as ->.
                pose proof L3 as l;apply Nat.lt_asymm,Nat.ltb_nlt in l as ->.
                pose proof L4 as l;apply Nat.ltb_lt in l as ->.
                rewrite <- HeqS,<-HeqU.
                destruct u' as [U1|];[|discriminate].
                intros E E';inversion E;inversion E';repeat split;exists U1;tauto.
             ++ repeat split;try reflexivity.
                cut (rebox (S k) (sp_clean (S3 ⋅ (t ⋅ U1)))
                           ≡ (rebox (S k) (sp_clean ((S3 ⋅ t) ⋅ U1))));
                  [intros (_&h&_);unfold π2 at 1 3;simpl;rewrite HeqM; rewrite h;auto|].
                apply IHk.
                ** revert h__size ht1 hs1 hu1.
                   replace (rebox (S k) t) with (rebox k t) in *
                     by (rewrite <- (sp_clean_idem Ct), <- (@rebox_switch k (S k) t),
                         (sp_clean_idem Ct)
                          by (revert St Bt;clear;lia||auto);reflexivity).
                   rewrite <- HeqT.
                   simpl.
                   destruct T1,T3,S1,U3;simpl;clear;rsimpl;lia.
                ** auto.
                ** simpl.
                   rewrite <- ht2.
                   replace (rebox (S k) t) with (rebox k t) in *
                     by (rewrite <- (sp_clean_idem Ct), <- (@rebox_switch k (S k) t),
                         (sp_clean_idem Ct)
                          by (revert St Bt;clear;lia||auto);reflexivity).
                   revert hs3 ht3 hu3.
                   repeat rewrite bind_error_seq.
                   rewrite <- HeqT;clear.
                   simpl.
                   destruct T1,T3,S1,U3;simpl;clear;firstorder discriminate.
          -- rewrite <- htu2 in L1.
             simpl in L1.
             exfalso;revert L1 L3;clear.
             destruct TU3;simpl;lia.
        * assert (L2 : close (sp_bind u) <= open (sp_bind t))
            by (revert decX Bs Bt Bu L3 L1;clear;intros;revert L3 L1;simpl;
                rewrite close_prod  by (rewrite bind_error_seq;tauto);lia).
          apply Compare_dec.le_lt_eq_dec in L2 as [L2|L2].
          -- destruct k;[exfalso;revert Su;lia|].
             assert (L4: close (sp_bind u) < open (sp_bind(s⋅t)))
               by (revert decX Bs Bt Bu L3 L2 L1;clear;intros;revert L3 L2 L1;simpl;
                   rewrite close_prod  by (rewrite bind_error_seq;tauto);
                   rewrite open_prod  by (rewrite bind_error_seq;tauto);lia).
             replace (rebox (S k) t) with (rebox k t) in *
               by (rewrite <- (sp_clean_idem Ct), <- (@rebox_switch k (S k) t),
                   (sp_clean_idem Ct)
                    by (revert St Bt;clear;lia||auto);reflexivity).  
             assert (exists T1 T2 T3, rebox k t = (T1,T2,Some T3)) as (T1&T2&T3&ET).
             ++ destruct (rebox k t) as ((T1&T2)&[T3|]);[exists T1,T2,T3;reflexivity|].
                exfalso.
                revert L2;rewrite <- ht2 in *;clear.
                simpl;destruct T1;simpl;lia.
             ++ rewrite ET in *.
                assert (ETU: rebox (S k) (t⋅u) = (T1, T2, Some (T3 ⋅ u))).
                ** simpl;unfold prod_T.
                   pose proof L2 as l;apply Nat.ltb_lt in l as ->.
                   pose proof L2 as l;apply Nat.lt_asymm,Nat.ltb_nlt in l as ->.
                   rewrite ET;reflexivity.
                ** unfold prod_T.
                   rewrite L1,Nat.ltb_irrefl.
                   pose proof L4 as l;apply Nat.ltb_lt in l as ->.
                   pose proof L4 as l;apply Nat.lt_asymm,Nat.ltb_nlt in l as ->.
                   rewrite ETU.
                   replace (rebox (S k) s) with (rebox k s) in *
                     by (rewrite <- (sp_clean_idem Cs), <- (@rebox_switch k (S k) s),
                         (sp_clean_idem Cs)
                          by (revert Ss Bs;clear;lia||auto);reflexivity).
                   assert (exists S1 S2 S3, rebox k s = (S1,S2,S3)) as (S1&S2&S3&ES)
                       by (destruct (rebox k s) as ((S1&S2)&S3);exists S1,S2,S3;reflexivity).
                   rewrite ES,ETU in E1;unfold π1,π3 in E1;simpl in E1.
                   destruct T1 as [T1|],S3 as [S3|];
                     try (exfalso;revert E1;clear;firstorder discriminate).
                   --- assert (rebox (S k) (s⋅t) =
                               (S1, (S2 ⋅ ▢ (π2 (rebox k (sp_clean (S3 ⋅ T1)))))⋅ T2,
                                Some T3))
                       as ->
                         by (simpl;unfold prod_T;rewrite L3,Nat.ltb_irrefl;
                             rewrite ES,ET;reflexivity).
                       rewrite ES.
                       erewrite rebox_switch;[reflexivity| | |].
                       +++ revert ht3 hs3;rewrite ES;simpl.
                           rewrite bind_error_seq;clear.
                           destruct S1;tauto.
                       +++ rewrite ES in hs1.
                           revert hs1 ht1 h__size;clear.
                           simpl.
                           destruct S1;rsimpl;lia.
                       +++ rewrite ES in hs1.
                           revert hs1 ht1 h__size;clear.
                           simpl.
                           destruct S1;rsimpl;lia.
                   --- assert (rebox (S k) (s⋅t) = (S1, S2 ⋅ T2, Some T3)) as ->
                         by (simpl;unfold prod_T;rewrite L3,Nat.ltb_irrefl;
                             rewrite ES,ET;reflexivity).
                       rewrite ES;reflexivity.
          -- destruct k;[exfalso;revert Su;lia|].
             assert (L4: close (sp_bind u) = open (sp_bind(s⋅t)))
               by (revert decX Bs Bt Bu L3 L2 L1;clear;intros;revert L3 L2 L1;simpl;
                   rewrite close_prod  by (rewrite bind_error_seq;tauto);
                   rewrite open_prod  by (rewrite bind_error_seq;tauto);lia).
             clear E1.
             assert ((exists S1 S2 S3 T1 T2 T3 U1 U2 U3, rebox (S k) s = (S1,S2,Some S3)
                                                    /\ rebox (S k) t = (Some T1,T2,Some T3)
                                                    /\ rebox (S k) u = (Some U1,U2, U3))
                     \/ (exists S1 S2 T2 T3 U1 U2 U3, rebox (S k) s = (S1,S2,None)
                                                /\ rebox (S k) t = (None,T2,Some T3)
                                                /\ rebox (S k) u = (Some U1,U2,U3))
                     \/ (exists S1 S2 S3 T1 T2 U2 U3, rebox (S k) s = (S1,S2,Some S3)
                                                    /\ rebox (S k) t = (Some T1,T2,None)
                                                    /\ rebox (S k) u = (None,U2,U3))
                     \/ (exists S1 S2 T2 U2 U3, rebox (S k) s = (S1,S2,None)
                                          /\ rebox (S k) t = (None,T2,None)
                                          /\ rebox (S k) u = (None,U2,U3))) as D.
             ++ simpl in L1,L4.
                rewrite close_prod in L1 by (rewrite bind_error_seq;tauto);
                  rewrite open_prod in L4 by (rewrite bind_error_seq;tauto).
                destruct (rebox (S k) s) as ((S1&S2)&S3).
                destruct (rebox (S k) t) as ((T1&T2)&T3).
                destruct (rebox (S k) u) as ((U1&U2)&U3).
                rewrite <- ht2 in L1, L2, L3, L4. 
                rewrite <- hs2 in L1, L3, L4. 
                rewrite <- hu2 in L1, L2, L4.
                revert L1 L2 L3 L4.
                simpl;destruct S3 as[S3|],T1 as [T1|],T3 as [T3|],U1 as [U1|];simpl;clear;
                  (left;exists S1, S2, S3, T1, T2, T3, U1, U2, U3;repeat split;reflexivity)
                  ||(right;left;exists S1, S2, T2, T3, U1, U2, U3;repeat split;reflexivity)
                  ||(right;right;left;exists S1, S2,S3,T1, T2, U2, U3;repeat split;reflexivity)
                  ||(right;right;right;exists S1, S2, T2, U2, U3;repeat split;reflexivity)
                  || (intros ? ? ? ?;exfalso;destruct S1,U3;simpl in *;lia).
             ++ destruct D as [(S1&S2&S3&T1&T2&T3&U1&U2&U3&ES&ET&EU)
                              |[(S1&S2&T2&T3&U1&U2&U3&ES&ET&EU)
                               |[(S1&S2&S3&T1&T2&U2&U3&ES&ET&EU)
                                |(S1&S2&T2&U2&U3&ES&ET&EU)]]].
                ** unfold prod_T;rewrite L1,L4;repeat rewrite Nat.ltb_irrefl.
                   rewrite ES,EU.
                   cut (rebox (S k) (t⋅u)
                        = (Some T1,T2⋅▢(π2(rebox k (sp_clean (T3⋅U1))))⋅U2,U3)
                        /\ rebox (S k) (s⋅t)
                          = (S1,S2⋅▢(π2(rebox k (sp_clean (S3⋅T1))))⋅T2,Some T3)).
                   --- intros (-> & ->).
                       repeat split;try reflexivity.
                       repeat rewrite (@rebox_switch (S k) k).
                       +++ set (sp_clean (S3 ⋅ T1)) as st.
                           set (sp_clean (T3 ⋅ U1)) as tu.
                           unfold π2 at 1 4;simpl.
                           repeat rewrite bsp_eq_seq_ass;reflexivity.
                       +++ revert decX ht3 hu3;rewrite ET, EU;clear;simpl;intro.
                           rewrite bind_error_seq.
                           destruct U3;tauto.
                       +++ revert decX ht1 hu1 h__size;rewrite ET, EU;clear;simpl;intro.
                           destruct U3;rsimpl;lia.
                       +++ revert decX ht1 hu1 h__size;rewrite ET, EU;clear;simpl;intro.
                           destruct U3;rsimpl;lia.
                       +++ revert decX ht3 hs3;rewrite ET, ES;clear;simpl;intro.
                           rewrite bind_error_seq.
                           destruct S1;tauto.
                       +++ revert decX ht1 hs1 h__size;rewrite ET, ES;clear;simpl;intro.
                           destruct S1;rsimpl;lia.
                       +++ revert decX ht1 hs1 h__size;rewrite ET, ES;clear;simpl;intro.
                           destruct S1;rsimpl;lia.
                   --- split.
                       +++ simpl;unfold prod_T.
                           rewrite L2,Nat.ltb_irrefl.
                           replace (rebox (S k) t) with (rebox k t) in *
                             by (rewrite <- (sp_clean_idem Ct),
                                 <- (@rebox_switch k (S k) t),(sp_clean_idem Ct)
                                  by (revert St Bt;clear;lia||auto);reflexivity).
                           replace (rebox (S k) u) with (rebox k u) in *
                             by (rewrite <- (sp_clean_idem Cu),
                                 <- (@rebox_switch k (S k) u),(sp_clean_idem Cu)
                                  by (revert Su Bu;clear;lia||auto);reflexivity).
                           rewrite ET,EU;reflexivity.
                       +++ simpl;unfold prod_T.
                           rewrite L3,Nat.ltb_irrefl.
                           replace (rebox (S k) t) with (rebox k t) in *
                             by (rewrite <- (sp_clean_idem Ct),
                                 <- (@rebox_switch k (S k) t),(sp_clean_idem Ct)
                                  by (revert St Bt;clear;lia||auto);reflexivity).
                           replace (rebox (S k) s) with (rebox k s) in *
                             by (rewrite <- (sp_clean_idem Cs),
                                 <- (@rebox_switch k (S k) s),(sp_clean_idem Cs)
                                  by (revert Ss Bs;clear;lia||auto);reflexivity).
                           rewrite ET,ES;reflexivity.
                ** unfold prod_T;rewrite L1,L4;repeat rewrite Nat.ltb_irrefl.
                   rewrite ES,EU.
                   cut (rebox (S k) (t⋅u)
                        = (None,T2⋅▢(π2(rebox k (sp_clean (T3⋅U1))))⋅U2,U3)
                        /\ rebox (S k) (s⋅t)
                          = (S1,S2⋅T2,Some T3)).
                   --- intros (-> & ->).
                       repeat split;try reflexivity.
                       repeat rewrite (@rebox_switch (S k) k).
                       +++ set (sp_clean (T3 ⋅ U1)) as tu.
                           unfold π2 at 1 4;simpl.
                           repeat rewrite bsp_eq_seq_ass;reflexivity.
                       +++ revert decX ht3 hu3;rewrite ET, EU;clear;simpl;intro.
                           rewrite bind_error_seq.
                           destruct U3;tauto.
                       +++ revert decX ht1 hu1 h__size;rewrite ET, EU;clear;simpl;intro.
                           destruct U3;rsimpl;lia.
                       +++ revert decX ht1 hu1 h__size;rewrite ET, EU;clear;simpl;intro.
                           destruct U3;rsimpl;lia.
                   --- split.
                       +++ simpl;unfold prod_T.
                           rewrite L2,Nat.ltb_irrefl.
                           replace (rebox (S k) t) with (rebox k t) in *
                             by (rewrite <- (sp_clean_idem Ct),
                                 <- (@rebox_switch k (S k) t),(sp_clean_idem Ct)
                                  by (revert St Bt;clear;lia||auto);reflexivity).
                           replace (rebox (S k) u) with (rebox k u) in *
                             by (rewrite <- (sp_clean_idem Cu),
                                 <- (@rebox_switch k (S k) u),(sp_clean_idem Cu)
                                  by (revert Su Bu;clear;lia||auto);reflexivity).
                           rewrite ET,EU;reflexivity.
                       +++ simpl;unfold prod_T.
                           rewrite L3,Nat.ltb_irrefl.
                           replace (rebox (S k) t) with (rebox k t) in *
                             by (rewrite <- (sp_clean_idem Ct),
                                 <- (@rebox_switch k (S k) t),(sp_clean_idem Ct)
                                  by (revert St Bt;clear;lia||auto);reflexivity).
                           replace (rebox (S k) s) with (rebox k s) in *
                             by (rewrite <- (sp_clean_idem Cs),
                                 <- (@rebox_switch k (S k) s),(sp_clean_idem Cs)
                                  by (revert Ss Bs;clear;lia||auto);reflexivity).
                           rewrite ET,ES;reflexivity.
                ** unfold prod_T;rewrite L1,L4;repeat rewrite Nat.ltb_irrefl.
                   rewrite ES,EU.
                   cut (rebox (S k) (t⋅u)
                        = (Some T1,T2⋅U2,U3)
                        /\ rebox (S k) (s⋅t)
                          = (S1,S2⋅▢(π2(rebox k (sp_clean (S3⋅T1))))⋅T2,None)).
                   --- intros (-> & ->).
                       repeat split;try reflexivity.
                       repeat rewrite (@rebox_switch (S k) k).
                       +++ set (sp_clean (S3 ⋅ T1)) as st.
                           unfold π2 at 1 4;simpl.
                           repeat rewrite bsp_eq_seq_ass;reflexivity.
                       +++ revert decX ht3 hs3;rewrite ET, ES;clear;simpl;intro.
                           rewrite bind_error_seq.
                           destruct S1;tauto.
                       +++ revert decX ht1 hs1 h__size;rewrite ET, ES;clear;simpl;intro.
                           destruct S1;rsimpl;lia.
                       +++ revert decX ht1 hs1 h__size;rewrite ET, ES;clear;simpl;intro.
                           destruct S1;rsimpl;lia.
                   --- split.
                       +++ simpl;unfold prod_T.
                           rewrite L2,Nat.ltb_irrefl.
                           replace (rebox (S k) t) with (rebox k t) in *
                             by (rewrite <- (sp_clean_idem Ct),
                                 <- (@rebox_switch k (S k) t),(sp_clean_idem Ct)
                                  by (revert St Bt;clear;lia||auto);reflexivity).
                           replace (rebox (S k) u) with (rebox k u) in *
                             by (rewrite <- (sp_clean_idem Cu),
                                 <- (@rebox_switch k (S k) u),(sp_clean_idem Cu)
                                  by (revert Su Bu;clear;lia||auto);reflexivity).
                           rewrite ET,EU;reflexivity.
                       +++ simpl;unfold prod_T.
                           rewrite L3,Nat.ltb_irrefl.
                           replace (rebox (S k) t) with (rebox k t) in *
                             by (rewrite <- (sp_clean_idem Ct),
                                 <- (@rebox_switch k (S k) t),(sp_clean_idem Ct)
                                  by (revert St Bt;clear;lia||auto);reflexivity).
                           replace (rebox (S k) s) with (rebox k s) in *
                             by (rewrite <- (sp_clean_idem Cs),
                                 <- (@rebox_switch k (S k) s),(sp_clean_idem Cs)
                                  by (revert Ss Bs;clear;lia||auto);reflexivity).
                           rewrite ET,ES;reflexivity.
                ** unfold prod_T;rewrite L1,L4;repeat rewrite Nat.ltb_irrefl.
                   rewrite ES,EU.
                   cut (rebox (S k) (t⋅u) = (None,T2⋅U2,U3)
                        /\ rebox (S k) (s⋅t) = (S1,S2⋅T2,None)).
                   --- intros (-> & ->).
                       repeat split;try reflexivity.
                       unfold π2;simpl.
                       repeat rewrite bsp_eq_seq_ass;reflexivity.
                   --- split.
                       +++ simpl;unfold prod_T.
                           rewrite L2,Nat.ltb_irrefl.
                           replace (rebox (S k) t) with (rebox k t) in *
                             by (rewrite <- (sp_clean_idem Ct),
                                 <- (@rebox_switch k (S k) t),(sp_clean_idem Ct)
                                  by (revert St Bt;clear;lia||auto);reflexivity).
                           replace (rebox (S k) u) with (rebox k u) in *
                             by (rewrite <- (sp_clean_idem Cu),
                                 <- (@rebox_switch k (S k) u),(sp_clean_idem Cu)
                                  by (revert Su Bu;clear;lia||auto);reflexivity).
                           rewrite ET,EU;reflexivity.
                       +++ simpl;unfold prod_T.
                           rewrite L3,Nat.ltb_irrefl.
                           replace (rebox (S k) t) with (rebox k t) in *
                             by (rewrite <- (sp_clean_idem Ct),
                                 <- (@rebox_switch k (S k) t),(sp_clean_idem Ct)
                                  by (revert St Bt;clear;lia||auto);reflexivity).
                           replace (rebox (S k) s) with (rebox k s) in *
                             by (rewrite <- (sp_clean_idem Cs),
                                 <- (@rebox_switch k (S k) s),(sp_clean_idem Cs)
                                  by (revert Ss Bs;clear;lia||auto);reflexivity).
                           rewrite ET,ES;reflexivity.
    - intros B.
      simpl in B.
      unfold Rebox.
      destruct (sp_clean_dec_par s t) as
          [(Es&Et&E1) | [ (Es&Et&E1) |  [ (Es&Et&E1) | (Es&Et&E1) ] ] ] ;
        destruct (sp_clean_dec_par t u)
        as [(Et'&Eu&E2)|[(Et'&Eu&E2)|[(Et'&Eu&E2)|(Et'&Eu&E2)]]];
        try (exfalso;(rewrite Et' in Et;revert Et;clear;simpl; tauto)
                     ||(rewrite Et in Et';revert Et';clear;simpl;tauto));
        repeat (rewrite sp_clean_par_left by
                   (try rewrite E1||rewrite E2;assumption||reflexivity))
        || (rewrite sp_clean_par_right by
              (try rewrite E1||rewrite E2;assumption||reflexivity))
        || (rewrite sp_clean_par_clean by
              (try rewrite E1||rewrite E2;simpl in *;tauto));
        simpl;try reflexivity.
      revert L;intro Ek;simpl in Ek.
      simpl;repeat split.
      destruct k as [|];
        try (rsimpl in *;apply is_sp_clean_sp_size in Es;
             apply is_sp_clean_sp_size in Et;
             apply is_sp_clean_sp_size in Eu;
             rewrite <-(sp_size_proper(sp_clean_eq _)) in Es;
             rewrite <-(sp_size_proper(sp_clean_eq _)) in Et;
             rewrite <-(sp_size_proper(sp_clean_eq _)) in Eu;rsimpl;lia).
      remember (S k) as K;rewrite HeqK at 2 3;simpl.
      unfold π2 at 1 3 6 7;simpl.
      apply bind_error_par in B as (Bs&B).
      apply bind_error_par in B as (Bt&Bu).
      apply is_sp_clean_sp_size in Es.
      apply is_sp_clean_sp_size in Et.
      apply is_sp_clean_sp_size in Eu.
      rewrite <- (sp_size_proper (sp_clean_eq _)) in Es.
      rewrite <- (sp_size_proper (sp_clean_eq _)) in Et.
      rewrite <- (sp_size_proper (sp_clean_eq _)) in Eu.
      repeat rewrite (@rebox_switch K k) by (auto||(rsimpl in *;lia)).
      apply mon_assoc.
    - intros B.
      simpl in B.
      destruct (sp_clean_dec_par s t) as
          [(Es&Et&->) | [ (Es&Et&->) |  [ (Es&Et&->) | (Es&Et&->) ] ] ] ;
        try ((rewrite sp_clean_par_left by assumption)
             || (rewrite sp_clean_par_right by assumption);simpl;
             try rewrite Es;try rewrite Et;reflexivity).
      rewrite sp_clean_par_clean by assumption.
      revert L;intro Ek;simpl.
      repeat split.
      unfold π2 at 1 4;simpl;auto.
    - simpl;rewrite left_unit.
      unfold Rebox.
      simpl;reflexivity.
    - simpl;rewrite right_unit.
      unfold Rebox;simpl.
      destruct (sp_clean s);reflexivity.
    - simpl;rewrite left_unit.
      unfold Rebox.
      simpl;reflexivity.
  Qed.

  Lemma rebox_unit k : rebox k 𝟭 = (None,𝟭,None).
  Proof. destruct k;reflexivity. Qed.
    
  Lemma Rebox_unbox s : s ≡ π2 (Rebox (unbox s)).
  Proof.
    cut (exists t, Rebox (unbox s) = (None,t,None) /\ s ≡ t);
      [intros (t&->&E);apply E|].
    induction s;try reflexivity.
    - simpl;destruct IHs1 as (t1&R1&Et1),IHs2 as (t2&R2&Et2).
      replace bsp_seq with prod by reflexivity.
      unfold Rebox in *.
      destruct (sp_clean_is_sp_clean (unbox s1)) as [E1|C1];
        destruct (sp_clean_is_sp_clean (unbox s2)) as [E2|C2].
      + rewrite E1,rebox_unit in R1;rewrite E2,rebox_unit in R2.
        exists 𝟭;split;[|rewrite Et1,Et2;inversion R1;inversion R2;auto].
        rewrite sp_clean_seq_left,E1 by assumption.
        apply rebox_unit.
      + rewrite E1,rebox_unit in R1.
        exists t2;split;[|rewrite Et1,Et2;inversion R1;inversion R2;auto].
        rewrite sp_clean_seq_right by assumption.
        erewrite rebox_switch;[eassumption| | |].
        * pose proof (unbox_bind s2) as E.
          intros E';rewrite E' in E;destruct E as [E|[E|E]];inversion E.
        * rsimpl;lia.
        * reflexivity.
      + rewrite E2,rebox_unit in R2.
        exists t1;split;[|rewrite Et1,Et2;inversion R1;inversion R2;auto].
        rewrite sp_clean_seq_left by assumption.
        erewrite rebox_switch;[eassumption| | |].
        * pose proof (unbox_bind s1) as E.
          intros E';rewrite E' in E;destruct E as [E|[E|E]];inversion E.
        * rsimpl;lia.
        * reflexivity.
      + exists (t1⋅t2);split;[|rewrite <- Et1,<-Et2;reflexivity].
        rewrite sp_clean_seq_clean by assumption.
        case_eq ⎢unbox s1⋅unbox s2⎥.
        * intro F;exfalso.
          apply is_sp_clean_sp_size in C1;apply is_sp_clean_sp_size in C2.
          rewrite <- (sp_size_proper(sp_clean_eq _)) in C1.
          rewrite <- (sp_size_proper(sp_clean_eq _)) in C2.
          rsimpl in F;lia.
        * intros k Ek;simpl.
          unfold prod_T.
          cut (rebox k (sp_clean (unbox s1)) = (None,t1,None)
               /\ rebox k (sp_clean (unbox s2)) = (None,t2,None)).
          -- intros (E'1&E'2);rewrite E'1,E'2.
             replace (close (sp_bind (sp_clean (unbox s2)))) with 0;
               [replace (open (sp_bind (sp_clean (unbox s1)))) with 0|].
             ++ simpl;reflexivity.
             ++ pose proof (@rebox_invariants k (sp_clean (unbox s1))) as (_&_&<-&_).
                ** apply is_sp_clean_sp_size in C2.
                   rewrite <- (sp_size_proper(sp_clean_eq _)) in C2.
                   rewrite <- (sp_size_proper(sp_clean_eq _)).
                   revert Ek;rsimpl;lia.
                ** assumption.
                ** rewrite <- (sp_bind_proper(sp_clean_eq _)).
                   pose proof (unbox_bind s1) as E.
                   intros E';rewrite E' in E;destruct E as [E|[E|E]];inversion E.
                ** rewrite E'1;reflexivity.
             ++ pose proof (@rebox_invariants k (sp_clean (unbox s2))) as (_&_&<-&_).
                ** apply is_sp_clean_sp_size in C1.
                   rewrite <- (sp_size_proper(sp_clean_eq _)) in C1.
                   rewrite <- (sp_size_proper(sp_clean_eq _)).
                   revert Ek;rsimpl;lia.
                ** assumption.
                ** rewrite <- (sp_bind_proper(sp_clean_eq _)).
                   pose proof (unbox_bind s2) as E.
                   intros E';rewrite E' in E;destruct E as [E|[E|E]];inversion E.
                ** rewrite E'2;reflexivity.
          -- split.
             ++ rewrite <- R1;apply rebox_switch;auto.
                ** pose proof (unbox_bind s1) as E.
                   intros E';rewrite E' in E;destruct E as [E|[E|E]];inversion E.
                ** apply is_sp_clean_sp_size in C2.
                   rewrite <- (sp_size_proper(sp_clean_eq _)) in C2.
                   revert Ek;rsimpl;lia.
             ++ rewrite <- R2;apply rebox_switch;auto.
                ** pose proof (unbox_bind s2) as E.
                   intros E';rewrite E' in E;destruct E as [E|[E|E]];inversion E.
                ** apply is_sp_clean_sp_size in C1.
                   rewrite <- (sp_size_proper(sp_clean_eq _)) in C1.
                   revert Ek;rsimpl;lia.
    - simpl;destruct IHs1 as (t1&R1&Et1),IHs2 as (t2&R2&Et2).
      replace bsp_par with par by reflexivity.
      unfold Rebox in *.
      destruct (sp_clean_is_sp_clean (unbox s1)) as [E1|C1];
        destruct (sp_clean_is_sp_clean (unbox s2)) as [E2|C2].
      + rewrite E1,rebox_unit in R1;rewrite E2,rebox_unit in R2.
        exists 𝟭;split;[|rewrite Et1,Et2;inversion R1;inversion R2;auto].
        rewrite sp_clean_par_left,E1 by assumption.
        apply rebox_unit.
      + rewrite E1,rebox_unit in R1.
        exists t2;split;[|rewrite Et1,Et2;inversion R1;inversion R2;auto].
        rewrite sp_clean_par_right by assumption.
        erewrite rebox_switch;[eassumption| | |].
        * pose proof (unbox_bind s2) as E.
          intros E';rewrite E' in E;destruct E as [E|[E|E]];inversion E.
        * rsimpl;lia.
        * reflexivity.
      + rewrite E2,rebox_unit in R2.
        exists t1;split;[|rewrite Et1,Et2;inversion R1;inversion R2;auto].
        rewrite sp_clean_par_left by assumption.
        erewrite rebox_switch;[eassumption| | |].
        * pose proof (unbox_bind s1) as E.
          intros E';rewrite E' in E;destruct E as [E|[E|E]];inversion E.
        * rsimpl;lia.
        * reflexivity.
        * rewrite right_unit;reflexivity.
      + exists (t1∥t2);split;[|rewrite <- Et1,<-Et2;reflexivity].
        rewrite sp_clean_par_clean by assumption.
        case_eq ⎢unbox s1∥unbox s2⎥.
        * intro F;exfalso.
          apply is_sp_clean_sp_size in C1;apply is_sp_clean_sp_size in C2.
          rewrite <- (sp_size_proper(sp_clean_eq _)) in C1.
          rewrite <- (sp_size_proper(sp_clean_eq _)) in C2.
          rsimpl in F;lia.
        * intros k Ek;simpl.
          erewrite rebox_switch,R1,rebox_switch,R2.
          -- reflexivity.
          -- pose proof (unbox_bind s2) as E.
             intros E';rewrite E' in E;destruct E as [E|[E|E]];inversion E.
          -- apply is_sp_clean_sp_size in C1.
             rewrite <- (sp_size_proper(sp_clean_eq _)) in C1.
             revert Ek;rsimpl;lia.
          -- reflexivity.
          -- pose proof (unbox_bind s1) as E.
             intros E';rewrite E' in E;destruct E as [E|[E|E]];inversion E.
          -- apply is_sp_clean_sp_size in C2.
             rewrite <- (sp_size_proper(sp_clean_eq _)) in C2.
             revert Ek;rsimpl;lia.
          -- reflexivity.
    - exists (bsp_var x);split;reflexivity.
    - simpl;destruct IHs as (t&R&Et).
      unfold Rebox in *.
      destruct (sp_clean_is_sp_clean (unbox s)) as [E|C].
      +  exists (𝟭⋅▢t⋅𝟭);split;[|rewrite left_unit,right_unit,Et;reflexivity].
         rewrite E in R.
        rewrite rebox_unit in R;inversion R;subst.
        rewrite sp_clean_seq_clean,sp_clean_seq_left.
        * rsimpl; replace ⎢unbox s⎥ with 0.
          -- unfold prod_T;simpl;reflexivity.
          -- rewrite (sp_size_proper(sp_clean_eq _)),E;reflexivity.
        * assumption.
        * rewrite sp_clean_seq_left by assumption.
          simpl;tauto.
        * simpl;tauto.
      + repeat rewrite sp_clean_seq_clean;try (simpl in *;tauto).
        rsimpl.
        unfold prod_T.
        replace (close (sp_bind VClose)) with 1 by reflexivity.
        replace (open (sp_bind (VOpen ⋅ sp_clean (unbox s)))) with 1.
        * rewrite Nat.ltb_irrefl.
          replace (rebox (⎢unbox s⎥+1) VClose) with ((Some 𝟭,𝟭,None) : T)
            by (destruct ⎢unbox s⎥;reflexivity).
          replace (rebox (⎢unbox s⎥+1) (VOpen⋅sp_clean(unbox s)))
            with ((None,𝟭,Some (𝟭⋅sp_clean(unbox s))) : T).
          -- simpl;rewrite sp_clean_idem by assumption.
             exists (𝟭⋅▢t⋅𝟭).
             split;[|rewrite left_unit,right_unit,Et;reflexivity].
             repeat f_equal.
             transitivity (π2 (rebox (⎢unbox s⎥ + 1) (sp_clean (unbox s))));
               [destruct (sp_clean(unbox s));reflexivity|].
             erewrite rebox_switch,R.
             ++ reflexivity.
             ++ destruct (unbox_bind s) as [<-|[<-|F]];simpl in *;tauto||discriminate.
             ++ lia.
             ++ reflexivity.
          -- replace (⎢unbox s⎥ + 1) with (S ⎢unbox s⎥) by lia.
             simpl;unfold prod_T.
             rewrite R.
             replace (rebox ⎢unbox s⎥ VOpen) with ((None,𝟭,Some 𝟭) : T)
               by (apply is_sp_clean_sp_size in C;
                   rewrite <- (sp_size_proper (sp_clean_eq _)) in C;
                   destruct ⎢unbox s⎥;reflexivity||lia).
             replace (close (sp_bind (sp_clean (unbox s)))) with 0.
             ++ simpl;reflexivity.
             ++ rewrite <- (sp_bind_proper(sp_clean_eq _)).
                destruct (unbox_bind s) as [<-|[<-|F]];simpl in *;reflexivity||tauto.
        * simpl.
          rewrite <- (sp_bind_proper(sp_clean_eq _)).
          destruct (unbox_bind s) as [<-|[<-|F]];simpl in *;reflexivity||tauto.
    - exists 𝟭;split;reflexivity.
  Qed.

  Definition Unbox s := unbox (bsp_clean s).
  Theorem eq_iff_unbox_eq s t : s ≡ t <-> Unbox s ≡ Unbox t.
  Proof.
    split.
    - intro E;apply bsp_clean_proper in E.
      revert E;apply unbox_proper.
    - intro E.
      rewrite bsp_clean_eq,(bsp_clean_eq t).
      rewrite Rebox_unbox,(Rebox_unbox (bsp_clean t)).
      apply Rebox_equiv in E;[apply E|].
      unfold Unbox.
      destruct (unbox_bind (bsp_clean s)) as [<-|[<-|F]];simpl in *;tauto||discriminate.
  Qed.
End encoding.