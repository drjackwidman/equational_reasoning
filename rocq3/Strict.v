(** * Strict.v
    Adequacy: the models of EqCat∞ are exactly the strict ω-categories.

    Both notions are stated over the same data, an [OmegaSig]: cells with
    an equality and a dimension, source, target and identity maps, and a
    partial composition ∘_k for every k.

      - [IsEqCatModel] ([Adequacy.v]) is the paper's axiomatization. Its
        laws are one-step: they mention a single [csrc], [ctgt] or [cid],
        except for the unit laws.
      - [IsStrictOmegaCat] (this file) is the classical description: the
        cells form a globular set, for every pair of levels l < k the
        k-cells form a category over the l-cells, and for every triple
        m < l < k the k-cells, l-cells and m-cells form a strict
        2-category. Its laws are stated between levels, so they mention
        the iterates src^c, tgt^c, id^c with c = k - l.

    [adequacy] proves the two equivalent. Left to right is an induction on
    the codimension c for each law; right to left takes c = 1.

    The category and 2-category laws are written out directly for the
    cells of the signature. They are not obtained by instantiating a
    general definition of category or 2-category from a library.

    The interchange law of a 2-category relates two different
    compositions. [exchange_same_level_commutes] shows why the exchange
    axiom must not be stated for a composition with itself. *)

Require Import Arith PeanoNat Lia.
Require Import Syntax Axioms Meta NormalForm Model FreeModel Decidable Reflect Adequacy.
Require Import Functor ModelLemmas.

Section Classical.
Context (Sg : OmegaSig).

(** ** The classical definition *)

(** Graded cells: equality is an equivalence, the operations respect it,
    and they shift the dimension as expected. *)
Record IsGradedCells : Prop := {
  g_refl  : forall a : Cell Sg, ceq a a;
  g_sym   : forall a b : Cell Sg, ceq a b -> ceq b a;
  g_trans : forall a b c : Cell Sg, ceq a b -> ceq b c -> ceq a c;
  g_dim_ceq  : forall a b : Cell Sg, ceq a b -> cdim a = cdim b;
  g_src_ceq  : forall a b : Cell Sg, cdim a > 0 -> ceq a b -> ceq (csrc a) (csrc b);
  g_tgt_ceq  : forall a b : Cell Sg, cdim a > 0 -> ceq a b -> ceq (ctgt a) (ctgt b);
  g_id_ceq   : forall a b : Cell Sg, ceq a b -> ceq (cid a) (cid b);
  g_comp_ceq : forall (k : nat) (a b a' b' : Cell Sg) H1 H2 H3 H1' H2' H3',
      ceq a a' -> ceq b b' ->
      ceq (ccomp k a b H1 H2 H3) (ccomp k a' b' H1' H2' H3');
  g_dim_src  : forall a : Cell Sg, cdim a > 0 -> cdim (csrc a) = cdim a - 1;
  g_dim_tgt  : forall a : Cell Sg, cdim a > 0 -> cdim (ctgt a) = cdim a - 1;
  g_dim_id   : forall a : Cell Sg, cdim (cid a) = S (cdim a);
  g_dim_comp : forall (k : nat) (a b : Cell Sg) H1 H2 H3, cdim (ccomp k a b H1 H2 H3) = cdim a
}.

(** Globular set: src src = src tgt and tgt src = tgt tgt. *)
Record IsGlobularSet : Prop := {
  gl_src : forall a : Cell Sg, cdim a >= 2 -> ceq (csrc (csrc a)) (csrc (ctgt a));
  gl_tgt : forall a : Cell Sg, cdim a >= 2 -> ceq (ctgt (csrc a)) (ctgt (ctgt a))
}.

(** The (l+c)-cells form a category over the l-cells: source src^c, target
    tgt^c, identity id^c, composition ∘_l. *)
Record IsCategoryAt (l c : nat) : Prop := {
  cat_src_id : forall x : Cell Sg, cdim x = l ->
      ceq (Nat.iter c csrc (Nat.iter c cid x)) x;
  cat_tgt_id : forall x : Cell Sg, cdim x = l ->
      ceq (Nat.iter c ctgt (Nat.iter c cid x)) x;
  cat_src_comp : forall (a b : Cell Sg) H1 H2 H3, cdim a = l + c ->
      ceq (Nat.iter c csrc (ccomp l a b H1 H2 H3)) (Nat.iter c csrc b);
  cat_tgt_comp : forall (a b : Cell Sg) H1 H2 H3, cdim a = l + c ->
      ceq (Nat.iter c ctgt (ccomp l a b H1 H2 H3)) (Nat.iter c ctgt a);
  cat_assoc : forall (a b d : Cell Sg) Hab1 Hab2 Hab3 Hl1 Hl2 Hl3 Hbd1 Hbd2 Hbd3 Hr1 Hr2 Hr3,
      cdim a = l + c ->
      ceq (ccomp l (ccomp l a b Hab1 Hab2 Hab3) d Hl1 Hl2 Hl3)
          (ccomp l a (ccomp l b d Hbd1 Hbd2 Hbd3) Hr1 Hr2 Hr3);
  cat_unit_r : forall (a : Cell Sg) H1 H2 H3, cdim a = l + c ->
      ceq (ccomp l a (Nat.iter c cid (Nat.iter c csrc a)) H1 H2 H3) a;
  cat_unit_l : forall (a : Cell Sg) H1 H2 H3, cdim a = l + c ->
      ceq (ccomp l (Nat.iter c cid (Nat.iter c ctgt a)) a H1 H2 H3) a
}.

(** The (l+c)-cells, l-cells and m-cells, m < l, form a strict 2-category:
    horizontal composition ∘_m is compatible with the source, target and
    identity of the category of (l+c)-cells over l-cells, and with its
    composition ∘_l (interchange). The three categories involved are given
    by [IsCategoryAt]. *)
Record Is2CategoryAt (m l c : nat) : Prop := {
  two_src : forall (a b : Cell Sg) H1 H2 H3 H1' H2' H3', cdim a = l + c ->
      ceq (Nat.iter c csrc (ccomp m a b H1 H2 H3))
          (ccomp m (Nat.iter c csrc a) (Nat.iter c csrc b) H1' H2' H3');
  two_tgt : forall (a b : Cell Sg) H1 H2 H3 H1' H2' H3', cdim a = l + c ->
      ceq (Nat.iter c ctgt (ccomp m a b H1 H2 H3))
          (ccomp m (Nat.iter c ctgt a) (Nat.iter c ctgt b) H1' H2' H3');
  two_id : forall (f g : Cell Sg) H1 H2 H3 H1' H2' H3', cdim f = l ->
      ceq (Nat.iter c cid (ccomp m f g H1 H2 H3))
          (ccomp m (Nat.iter c cid f) (Nat.iter c cid g) H1' H2' H3');
  two_interchange : forall (a b a' b' : Cell Sg)
      Hab1 Hab2 Hab3 Hab1' Hab2' Hab3' HL1 HL2 HL3
      Haa1 Haa2 Haa3 Hbb1 Hbb2 Hbb3 HR1 HR2 HR3,
      cdim a = l + c ->
      ceq (ccomp m (ccomp l a b Hab1 Hab2 Hab3) (ccomp l a' b' Hab1' Hab2' Hab3') HL1 HL2 HL3)
          (ccomp l (ccomp m a a' Haa1 Haa2 Haa3) (ccomp m b b' Hbb1 Hbb2 Hbb3) HR1 HR2 HR3)
}.

(** A strict ω-category: a globular set in which every pair of levels is a
    category and every triple of levels is a strict 2-category. *)
Definition IsStrictOmegaCat : Prop :=
  IsGradedCells /\ IsGlobularSet /\
  (forall l c, 1 <= c -> IsCategoryAt l c) /\
  (forall m l c, m < l -> 1 <= c -> Is2CategoryAt m l c).

(** ** Models are strict ω-categories *)
Theorem model_is_strict : IsEqCatModel Sg -> IsStrictOmegaCat.
Proof.
  intro M. split; [| split; [| split]].
  - constructor.
    + apply (ceq_refl Sg M).
    + apply (ceq_sym Sg M).
    + apply (ceq_trans Sg M).
    + apply (cdim_ceq Sg M).
    + apply (csrc_ceq Sg M).
    + apply (ctgt_ceq Sg M).
    + apply (cid_ceq Sg M).
    + apply (ccomp_ceq Sg M).
    + apply (cdim_src Sg M).
    + apply (cdim_tgt Sg M).
    + apply (cdim_id Sg M).
    + apply (cdim_comp Sg M).
  - constructor; [apply (glob_src Sg M) | apply (glob_tgt Sg M)].
  - intros l c Hc. constructor.
    + intros x _. apply (iter_src_id_cancel Sg M).
    + intros x _. apply (iter_tgt_id_cancel Sg M).
    + intros a b H1 H2 H3 Hd. apply (src_comp_top_iter Sg M); assumption.
    + intros a b H1 H2 H3 Hd. apply (tgt_comp_top_iter Sg M); assumption.
    + intros. apply (assoc Sg M).
    + intros a H1 H2 H3 Hd.
      assert (X : cidext_src (cdim a - l) a = Nat.iter c cid (Nat.iter c csrc a))
        by (unfold cidext_src; replace (cdim a - l) with c by lia; reflexivity).
      pose proof (unit_r Sg M l a) as U. rewrite X in U. apply U.
    + intros a H1 H2 H3 Hd.
      assert (X : cidext_tgt (cdim a - l) a = Nat.iter c cid (Nat.iter c ctgt a))
        by (unfold cidext_tgt; replace (cdim a - l) with c by lia; reflexivity).
      pose proof (unit_l Sg M l a) as U. rewrite X in U. apply U.
  - intros m l c Hml Hc. constructor.
    + intros a b H1 H2 H3 H1' H2' H3' Hd. apply (src_comp_low_iter Sg M). lia.
    + intros a b H1 H2 H3 H1' H2' H3' Hd. apply (tgt_comp_low_iter Sg M). lia.
    + intros f g H1 H2 H3 H1' H2' H3' Hd. apply (id_comp_iter Sg M).
    + intros. apply (exchange Sg M). lia.
Qed.

(** ** Strict ω-categories are models *)
Theorem strict_is_model : IsStrictOmegaCat -> IsEqCatModel Sg.
Proof.
  intros (G & Gl & C & T). constructor.
  - apply (g_refl G).
  - apply (g_sym G).
  - apply (g_trans G).
  - apply (g_dim_ceq G).
  - apply (g_src_ceq G).
  - apply (g_tgt_ceq G).
  - apply (g_id_ceq G).
  - apply (g_comp_ceq G).
  - apply (g_dim_src G).
  - apply (g_dim_tgt G).
  - apply (g_dim_id G).
  - apply (g_dim_comp G).
  - apply (gl_src Gl).
  - apply (gl_tgt Gl).
  - intro a. exact (cat_src_id _ _ (C (cdim a) 1 ltac:(lia)) a eq_refl).
  - intro a. exact (cat_tgt_id _ _ (C (cdim a) 1 ltac:(lia)) a eq_refl).
  - intros k a b H1 H2 H3 Hd.
    exact (cat_src_comp _ _ (C k 1 ltac:(lia)) a b H1 H2 H3 ltac:(lia)).
  - intros k a b H1 H2 H3 Hd.
    exact (cat_tgt_comp _ _ (C k 1 ltac:(lia)) a b H1 H2 H3 ltac:(lia)).
  - intros k a b H1 H2 H3 H1' H2' H3' Hd.
    exact (two_src _ _ _ (T k (cdim a - 1) 1 ltac:(lia) ltac:(lia)) a b
             H1 H2 H3 H1' H2' H3' ltac:(lia)).
  - intros k a b H1 H2 H3 H1' H2' H3' Hd.
    exact (two_tgt _ _ _ (T k (cdim a - 1) 1 ltac:(lia) ltac:(lia)) a b
             H1 H2 H3 H1' H2' H3' ltac:(lia)).
  - intros k a b c Hab1 Hab2 Hab3 Hl1 Hl2 Hl3 Hbc1 Hbc2 Hbc3 Hr1 Hr2 Hr3.
    apply (cat_assoc _ _ (C k (cdim a - k) ltac:(lia))). lia.
  - intros m n x y z w Hxy1 Hxy2 Hxy3 Hzw1 Hzw2 Hzw3 HL1 HL2 HL3
           Hxz1 Hxz2 Hxz3 Hyw1 Hyw2 Hyw3 HR1 HR2 HR3 Hmn.
    destruct (Nat.lt_ge_cases m n) as [Hlt | Hge].
    + apply (two_interchange _ _ _ (T m n (cdim x - n) Hlt ltac:(lia))). lia.
    + apply (g_sym G).
      apply (two_interchange _ _ _ (T n m (cdim x - m) ltac:(lia) ltac:(lia))). lia.
  - intros k a H1 H2 H3.
    apply (cat_unit_r _ _ (C k (cdim a - k) ltac:(lia))). lia.
  - intros k a H1 H2 H3.
    assert (Hk : k < cdim a) by (rewrite <- H1; exact H2).
    apply (cat_unit_l _ _ (C k (cdim a - k) ltac:(lia))). lia.
  - intros k a b H1 H2 H3 H1' H2' H3'.
    exact (two_id _ _ _ (T k (cdim a) 1 H2 ltac:(lia)) a b H1 H2 H3 H1' H2' H3' eq_refl).
Qed.

(** ** Adequacy *)
Theorem adequacy : IsEqCatModel Sg <-> IsStrictOmegaCat.
Proof. split; [apply model_is_strict | apply strict_is_model]. Qed.

(** ** Why exchange is only between distinct levels *)

(** Exchange between ∘_k and itself. *)
Definition exchange_same_level (k : nat) : Prop :=
  forall (x y z w : Cell Sg)
    Hxy1 Hxy2 Hxy3 Hzw1 Hzw2 Hzw3 HL1 HL2 HL3 Hxz1 Hxz2 Hxz3 Hyw1 Hyw2 Hyw3 HR1 HR2 HR3,
    ceq (ccomp k (ccomp k x y Hxy1 Hxy2 Hxy3) (ccomp k z w Hzw1 Hzw2 Hzw3) HL1 HL2 HL3)
        (ccomp k (ccomp k x z Hxz1 Hxz2 Hxz3) (ccomp k y w Hyw1 Hyw2 Hyw3) HR1 HR2 HR3).

(** If it held in a model, any two (k+1)-cells that are loops on the same
    k-cell would commute under ∘_k. So a one-object category with a
    noncommutative monoid of arrows could not be a model. *)
Theorem exchange_same_level_commutes : IsEqCatModel Sg -> forall k,
  exchange_same_level k ->
  forall p q : Cell Sg, cdim p = S k -> cdim q = S k ->
  ceq (csrc p) (ctgt p) -> ceq (csrc q) (ctgt q) -> ceq (csrc p) (csrc q) ->
  forall H1 H2 H3 H1' H2' H3',
  ceq (ccomp k p q H1 H2 H3) (ccomp k q p H1' H2' H3').
Proof.
  intros M k Hex p q Hp Hq Lp Lq Hpq H1 H2 H3 H1' H2' H3'.
  pose (sy := ceq_sym Sg M). pose (tr := ceq_trans Sg M). pose (rf := ceq_refl Sg M).
  set (e := cid (csrc p)).
  assert (De : cdim e = S k) by (apply (cdim_id_src Sg M); exact Hp).
  assert (Se : ceq (csrc e) (csrc p)) by apply (src_id Sg M).
  assert (Te : ceq (ctgt e) (csrc p)) by apply (tgt_id Sg M).
  assert (Tq : ceq (csrc p) (ctgt q)) by (apply (tr _ (csrc q) _); assumption).
  destruct (comp1_ok Sg k e p De Hp (tr _ _ _ Se Lp)) as (A1 & A2 & A3).
  destruct (comp1_ok Sg k q e Hq De (tr _ _ _ (sy _ _ Hpq) (sy _ _ Te))) as (B1 & B2 & B3).
  destruct (comp1_ok Sg k e q De Hq (tr _ _ _ Se Tq)) as (C1 & C2 & C3).
  destruct (comp1_ok Sg k p e Hp De (sy _ _ Te)) as (D1 & D2 & D3).
  assert (Uep : ceq (ccomp k e p A1 A2 A3) p) by (apply (unit_l1' Sg M k p (csrc p) Hp); exact Lp).
  assert (Uqe : ceq (ccomp k q e B1 B2 B3) q) by (apply (unit_r1' Sg M k q (csrc p) Hq); exact Hpq).
  assert (Ueq : ceq (ccomp k e q C1 C2 C3) q) by (apply (unit_l1' Sg M k q (csrc p) Hq); exact Tq).
  assert (Upe : ceq (ccomp k p e D1 D2 D3) p) by (apply (unit_r1' Sg M k p (csrc p) Hp); apply rf).
  assert (Dep : cdim (ccomp k e p A1 A2 A3) = S k) by (rewrite (cdim_comp Sg M); exact De).
  assert (Dqe : cdim (ccomp k q e B1 B2 B3) = S k) by (rewrite (cdim_comp Sg M); exact Hq).
  assert (Deq : cdim (ccomp k e q C1 C2 C3) = S k) by (rewrite (cdim_comp Sg M); exact De).
  assert (Dpe : cdim (ccomp k p e D1 D2 D3) = S k) by (rewrite (cdim_comp Sg M); exact Hp).
  assert (Bqp : ceq (csrc q) (ctgt p)) by (apply (tr _ (csrc p) _); [apply sy; exact Hpq | exact Lp]).
  assert (S1 : ceq (csrc (ccomp k e p A1 A2 A3)) (csrc p))
    by (apply (csrc_ceq Sg M); [lia | exact Uep]).
  assert (T1 : ceq (ctgt (ccomp k q e B1 B2 B3)) (ctgt q))
    by (apply (ctgt_ceq Sg M); [lia | exact Uqe]).
  assert (S2 : ceq (csrc (ccomp k e q C1 C2 C3)) (csrc q))
    by (apply (csrc_ceq Sg M); [lia | exact Ueq]).
  assert (T2 : ceq (ctgt (ccomp k p e D1 D2 D3)) (ctgt p))
    by (apply (ctgt_ceq Sg M); [lia | exact Upe]).
  destruct (comp1_ok Sg k _ _ Dep Dqe (tr _ _ _ S1 (tr _ _ _ Tq (sy _ _ T1)))) as (L1 & L2 & L3).
  destruct (comp1_ok Sg k _ _ Deq Dpe (tr _ _ _ S2 (tr _ _ _ Bqp (sy _ _ T2)))) as (R1 & R2 & R3).
  apply (tr _ (ccomp k (ccomp k e p A1 A2 A3) (ccomp k q e B1 B2 B3) L1 L2 L3) _).
  { apply (ccomp_ceq Sg M); apply sy; assumption. }
  apply (tr _ (ccomp k (ccomp k e q C1 C2 C3) (ccomp k p e D1 D2 D3) R1 R2 R3) _).
  { apply Hex. }
  apply (ccomp_ceq Sg M); assumption.
Qed.

End Classical.

Print Assumptions adequacy.
Print Assumptions exchange_same_level_commutes.
