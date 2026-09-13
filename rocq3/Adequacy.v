(** * Adequacy.v
    The free model satisfies the laws of EqCat∞, packaged as a structure.

    Two pieces:

    1. An abstract signature [OmegaSig] (cells with a setoid equality, a
       dimension, src/tgt/id, and a composition that is partial in the
       usual way: defined on pairs whose boundaries agree) and a record
       [IsEqCatModel] listing the laws of Figure 2 over it, up to the
       setoid equality: congruence (E1–E8), dimensions (D1–D4),
       globularity (IC1–2), identities (IC3–4), boundary of composites
       (IC5–8), associativity (IC9), exchange (IC10), unit laws (IC11–12),
       id/comp compatibility (IC13).

    2. [FreeModel_is_EqCat_model]: [FreeCell] with [===], [Free_src],
       [Free_tgt], [Free_id], [Free_comp] satisfies [IsEqCatModel]. Each
       law is one constructor of [eq_cat]; the well-formedness premises
       are exactly the [cell_proof] components of the cells involved.

    What this is: the standard well-definedness fact that the Lindenbaum
    quotient satisfies the equations it was quotiented by, stated with
    partial composition and setoid equality so that it reads as a
    structure rather than a term relation.

    What this is NOT: Theorem 6.1. That theorem compares this ℕ-indexed
    presentation with the classical definition of strict ω-category
    (each C_k ⇉ C_ℓ a category, each triple a strict 2-category, per
    Appendix B). Neither direction of that comparison is mechanized.
    See RESPONSE.md. *)

Require Import Arith PeanoNat Lia Bool.
Require Import Setoid Morphisms.
Require Import Syntax Axioms Meta NormalForm Model FreeModel Decidable Reflect.

(** ** 1. The abstract structure (independent of the generators). *)

Record OmegaSig : Type := {
  Cell  : Type;
  ceq   : Cell -> Cell -> Prop;
  cdim  : Cell -> nat;
  csrc  : Cell -> Cell;
  ctgt  : Cell -> Cell;
  cid   : Cell -> Cell;
  (** [ccomp k a b] is a ∘_k b. It takes the composability data as
      arguments: equal dimension, k below it, and the boundary equation
      src^{n-k} a = tgt^{n-k} b up to [ceq]. *)
  ccomp : forall (k : nat) (a b : Cell),
            cdim a = cdim b -> k < cdim a ->
            ceq (Nat.iter (cdim a - k) csrc a) (Nat.iter (cdim a - k) ctgt b) ->
            Cell
}.

Arguments ceq {_} _ _.  Arguments cdim {_} _.
Arguments csrc {_} _.   Arguments ctgt {_} _.   Arguments cid {_} _.
Arguments ccomp {_} _ _ _ _ _ _.

(** Iterated identity-extension of a boundary, used by the unit laws. *)
Definition cidext_src {Sg : OmegaSig} (c : nat) (a : Cell Sg) : Cell Sg :=
  Nat.iter c cid (Nat.iter c csrc a).
Definition cidext_tgt {Sg : OmegaSig} (c : nat) (a : Cell Sg) : Cell Sg :=
  Nat.iter c cid (Nat.iter c ctgt a).

Record IsEqCatModel (Sg : OmegaSig) : Prop := {
  (* --- equality is a congruence, dimension is invariant --- *)
  ceq_refl  : forall (a : Cell Sg), ceq a a;
  ceq_sym   : forall (a : Cell Sg) (b : Cell Sg), ceq a b -> ceq b a;
  ceq_trans : forall (a : Cell Sg) (b : Cell Sg) (c : Cell Sg), ceq a b -> ceq b c -> ceq a c;
  cdim_ceq  : forall (a : Cell Sg) (b : Cell Sg), ceq a b -> cdim a = cdim b;
  csrc_ceq  : forall (a : Cell Sg) (b : Cell Sg), cdim a > 0 -> ceq a b -> ceq (csrc a) (csrc b);
  ctgt_ceq  : forall (a : Cell Sg) (b : Cell Sg), cdim a > 0 -> ceq a b -> ceq (ctgt a) (ctgt b);
  cid_ceq   : forall (a : Cell Sg) (b : Cell Sg), ceq a b -> ceq (cid a) (cid b);
  ccomp_ceq : forall (k : nat) (a : Cell Sg) (b : Cell Sg) (a' : Cell Sg) (b' : Cell Sg) H1 H2 H3 H1' H2' H3',
      ceq a a' -> ceq b b' ->
      ceq (ccomp k a b H1 H2 H3) (ccomp k a' b' H1' H2' H3');

  (* --- dimensions (D1–D4) --- *)
  cdim_src  : forall (a : Cell Sg), cdim a > 0 -> cdim (csrc a) = cdim a - 1;
  cdim_tgt  : forall (a : Cell Sg), cdim a > 0 -> cdim (ctgt a) = cdim a - 1;
  cdim_id   : forall (a : Cell Sg), cdim (cid a) = S (cdim a);
  cdim_comp : forall (k : nat) (a : Cell Sg) (b : Cell Sg) H1 H2 H3, cdim (ccomp k a b H1 H2 H3) = cdim a;

  (* --- globularity (IC1, IC2) --- *)
  glob_src : forall (a : Cell Sg), cdim a >= 2 -> ceq (csrc (csrc a)) (csrc (ctgt a));
  glob_tgt : forall (a : Cell Sg), cdim a >= 2 -> ceq (ctgt (csrc a)) (ctgt (ctgt a));

  (* --- identities have the expected boundary (IC3, IC4) --- *)
  src_id : forall (a : Cell Sg), ceq (csrc (cid a)) a;
  tgt_id : forall (a : Cell Sg), ceq (ctgt (cid a)) a;

  (* --- boundary of a composite (IC5–IC8) --- *)
  src_comp_top : forall (k : nat) (a : Cell Sg) (b : Cell Sg) H1 H2 H3, cdim a = S k ->
      ceq (csrc (ccomp k a b H1 H2 H3)) (csrc b);
  tgt_comp_top : forall (k : nat) (a : Cell Sg) (b : Cell Sg) H1 H2 H3, cdim a = S k ->
      ceq (ctgt (ccomp k a b H1 H2 H3)) (ctgt a);
  src_comp_low : forall (k : nat) (a : Cell Sg) (b : Cell Sg) H1 H2 H3 H1' H2' H3', cdim a > S k ->
      ceq (csrc (ccomp k a b H1 H2 H3)) (ccomp k (csrc a) (csrc b) H1' H2' H3');
  tgt_comp_low : forall (k : nat) (a : Cell Sg) (b : Cell Sg) H1 H2 H3 H1' H2' H3', cdim a > S k ->
      ceq (ctgt (ccomp k a b H1 H2 H3)) (ccomp k (ctgt a) (ctgt b) H1' H2' H3');

  (* --- associativity (IC9) --- *)
  assoc : forall (k : nat) (a : Cell Sg) (b : Cell Sg) (c : Cell Sg) Hab1 Hab2 Hab3 Hl1 Hl2 Hl3 Hbc1 Hbc2 Hbc3 Hr1 Hr2 Hr3,
      ceq (ccomp k (ccomp k a b Hab1 Hab2 Hab3) c Hl1 Hl2 Hl3)
          (ccomp k a (ccomp k b c Hbc1 Hbc2 Hbc3) Hr1 Hr2 Hr3);

  (* --- exchange (IC10) --- *)
  exchange : forall (m : nat) (n : nat) (x : Cell Sg) (y : Cell Sg) (z : Cell Sg) (w : Cell Sg) Hxy1 Hxy2 Hxy3 Hzw1 Hzw2 Hzw3 HL1 HL2 HL3 Hxz1 Hxz2 Hxz3 Hyw1 Hyw2 Hyw3 HR1 HR2 HR3,
      ceq (ccomp m (ccomp n x y Hxy1 Hxy2 Hxy3) (ccomp n z w Hzw1 Hzw2 Hzw3) HL1 HL2 HL3)
          (ccomp n (ccomp m x z Hxz1 Hxz2 Hxz3) (ccomp m y w Hyw1 Hyw2 Hyw3) HR1 HR2 HR3);

  (* --- unit laws (IC11, IC12) --- *)
  unit_r : forall (k : nat) (a : Cell Sg) H1 H2 H3,
      ceq (ccomp k a (cidext_src (cdim a - k) a) H1 H2 H3) a;
  unit_l : forall (k : nat) (a : Cell Sg) H1 H2 H3,
      ceq (ccomp k (cidext_tgt (cdim a - k) a) a H1 H2 H3) a;

  (* --- id is a functor for composition (IC13) --- *)
  id_comp : forall (k : nat) (a : Cell Sg) (b : Cell Sg) H1 H2 H3 H1' H2' H3',
      ceq (cid (ccomp k a b H1 H2 H3)) (ccomp k (cid a) (cid b) H1' H2' H3')
}.

(** ** 2. The free model is a strict ω-category. *)

Module AdequacyF (G : GEN).
Include ReflectF G.

(** Projections of the totalized [Free_src]/[Free_tgt] on positive-dimensional
    cells, and of their iterates. *)
Lemma Free_src_pos : forall t d p,
  Free_src {| cell_term := t; cell_dim := S d; cell_proof := p |}
  = {| cell_term := src t; cell_dim := d; cell_proof := wf_src t d p |}.
Proof. reflexivity. Qed.

Lemma Free_tgt_pos : forall t d p,
  Free_tgt {| cell_term := t; cell_dim := S d; cell_proof := p |}
  = {| cell_term := tgt t; cell_dim := d; cell_proof := wf_tgt t d p |}.
Proof. reflexivity. Qed.

Lemma Free_src_proj : forall c, cell_dim c > 0 ->
  cell_term (Free_src c) = src (cell_term c) /\ cell_dim (Free_src c) = cell_dim c - 1.
Proof. intros [t [|d] p] H; simpl in H; [lia | split; [reflexivity | simpl; lia]]. Qed.

Lemma Free_tgt_proj : forall c, cell_dim c > 0 ->
  cell_term (Free_tgt c) = tgt (cell_term c) /\ cell_dim (Free_tgt c) = cell_dim c - 1.
Proof. intros [t [|d] p] H; simpl in H; [lia | split; [reflexivity | simpl; lia]]. Qed.

Lemma Free_iter_src_proj : forall n c, n <= cell_dim c ->
  cell_term (Nat.iter n Free_src c) = iter_src n (cell_term c)
  /\ cell_dim (Nat.iter n Free_src c) = cell_dim c - n.
Proof.
  induction n as [|n IH]; intros c Hn.
  - split; [reflexivity | simpl; lia].
  - destruct (IH c ltac:(lia)) as [Ht Hd].
    change (Nat.iter (S n) Free_src c) with (Free_src (Nat.iter n Free_src c)).
    destruct (Free_src_proj (Nat.iter n Free_src c) ltac:(lia)) as [Ht' Hd'].
    rewrite Ht', Hd', Ht, Hd. split; [reflexivity | lia].
Qed.

Lemma Free_iter_tgt_proj : forall n c, n <= cell_dim c ->
  cell_term (Nat.iter n Free_tgt c) = iter_tgt n (cell_term c)
  /\ cell_dim (Nat.iter n Free_tgt c) = cell_dim c - n.
Proof.
  induction n as [|n IH]; intros c Hn.
  - split; [reflexivity | simpl; lia].
  - destruct (IH c ltac:(lia)) as [Ht Hd].
    change (Nat.iter (S n) Free_tgt c) with (Free_tgt (Nat.iter n Free_tgt c)).
    destruct (Free_tgt_proj (Nat.iter n Free_tgt c) ltac:(lia)) as [Ht' Hd'].
    rewrite Ht', Hd', Ht, Hd. split; [reflexivity | lia].
Qed.

Lemma Free_iter_id_proj : forall n c,
  cell_term (Nat.iter n Free_id c) = iter_id n (cell_term c)
  /\ cell_dim (Nat.iter n Free_id c) = cell_dim c + n.
Proof.
  induction n as [|n IH]; intros c.
  - split; [reflexivity | simpl; lia].
  - destruct (IH c) as [Ht Hd].
    change (Nat.iter (S n) Free_id c) with (Free_id (Nat.iter n Free_id c)).
    simpl. rewrite Ht, Hd. split; [reflexivity | lia].
Qed.

(** Boundary equations, transported from the [Nat.iter Free_src] form used
    by [OmegaSig] to the term-level [iter_src] form used by [wf_comp]. *)
Lemma FreeSig_boundary : forall k (a b : FreeCell),
  cell_dim a = cell_dim b -> k < cell_dim a ->
  FreeCell_eq (Nat.iter (cell_dim a - k) Free_src a) (Nat.iter (cell_dim a - k) Free_tgt b) ->
  iter_src (cell_dim a - k) (cell_term a) == iter_tgt (cell_dim a - k) (cell_term b).
Proof.
  intros k a b Hd Hk H. unfold FreeCell_eq in H.
  destruct (Free_iter_src_proj (cell_dim a - k) a ltac:(lia)) as [Hs _].
  destruct (Free_iter_tgt_proj (cell_dim a - k) b ltac:(lia)) as [Ht _].
  rewrite Hs, Ht in H. exact H.
Qed.

(** The signature carried by the free model. [ccomp k a b] is a ∘_k b;
    [Free_comp] takes its operands in the order (right, left), and wants
    the boundary in term form, hence the [FreeSig_boundary] wrapper. *)
Definition FreeSig : OmegaSig := {|
  Cell  := FreeCell;
  ceq   := FreeCell_eq;
  cdim  := cell_dim;
  csrc  := Free_src;
  ctgt  := Free_tgt;
  cid   := Free_id;
  ccomp := fun k a b H1 H2 H3 => Free_comp k b a H1 H2 (FreeSig_boundary k a b H1 H2 H3)
|}.

(** Reduce the record projections of [FreeSig] in the goal. *)
Ltac red_sig :=
  cbv beta iota delta [FreeSig ceq ccomp cid csrc ctgt cdim Cell cidext_src cidext_tgt] in *.

(** Before unfolding [FreeCell_eq], record the [wf] proofs carried by the
    two cells of the goal. These are exactly the premises of the axioms. *)
Ltac wf_of_goal :=
  match goal with
  | |- FreeCell_eq ?L ?R =>
      pose proof (cell_proof L) as HL; pose proof (cell_proof R) as HR;
      simpl in HL, HR
  end.

Theorem FreeModel_is_EqCat_model : IsEqCatModel FreeSig.
Proof.
  constructor; intros; red_sig.
  - (* refl *) apply FreeCell_eq_refl.
  - (* sym *) apply FreeCell_eq_sym; assumption.
  - (* trans *) eapply FreeCell_eq_trans; eassumption.
  - (* dim *) destruct a as [ta da pa], b as [tb db pb].
    exact (eq_cat_dim_agree _ _ _ _ H pa pb).
  - (* src cong *) rewrite H0. apply FreeCell_eq_refl.
  - (* tgt cong *) rewrite H0. apply FreeCell_eq_refl.
  - (* id cong *) rewrite H. apply FreeCell_eq_refl.
  - (* comp cong: E7 *) wf_of_goal. unfold FreeCell_eq in *; simpl.
    apply (E7_comp _ _ _ _ k (cell_dim a)); [exact H | exact H0 | exact HL |].
    rewrite (eq_cat_dim_agree _ _ _ _ H (cell_proof a) (cell_proof a')). exact HR.
  - (* dim src *) destruct a as [t [|d] p]; simpl in *; lia.
  - (* dim tgt *) destruct a as [t [|d] p]; simpl in *; lia.
  - (* dim id *) reflexivity.
  - (* dim comp *) reflexivity.
  - (* glob src: IC1 *) destruct a as [t [|[|d]] p]; simpl in H; try lia.
    unfold FreeCell_eq; simpl. apply (IC1 t (S (S d)) p). lia.
  - (* glob tgt: IC2 *) destruct a as [t [|[|d]] p]; simpl in H; try lia.
    unfold FreeCell_eq; simpl. apply (IC2 t (S (S d)) p). lia.
  - (* src id: IC3 *) destruct a as [t d p]. unfold FreeCell_eq; simpl. apply (IC3 t d p).
  - (* tgt id: IC4 *) destruct a as [t d p]. unfold FreeCell_eq; simpl. apply (IC4 t d p).
  - (* src comp top: IC5 *)
    pose proof (cell_proof (Free_comp k b a H1 H2 (FreeSig_boundary k a b H1 H2 H3))) as Hwf.
    destruct a as [ta da pa], b as [tb db pb]; simpl in *. subst.
    unfold FreeCell_eq; simpl. apply IC5. exact Hwf.
  - (* tgt comp top: IC6 *)
    pose proof (cell_proof (Free_comp k b a H1 H2 (FreeSig_boundary k a b H1 H2 H3))) as Hwf.
    destruct a as [ta da pa], b as [tb db pb]; simpl in *. subst.
    unfold FreeCell_eq; simpl. apply IC6. exact Hwf.
  - (* src comp low: IC7 *)
    pose proof (cell_proof (Free_comp k b a H1 H2 (FreeSig_boundary k a b H1 H2 H3))) as Hwf.
    destruct a as [ta da pa], b as [tb db pb]; simpl in *. subst db.
    destruct da as [|da]; [lia|].
    unfold FreeCell_eq; simpl. apply (IC7 tb ta k (S da)); [exact Hwf | lia].
  - (* tgt comp low: IC8 *)
    pose proof (cell_proof (Free_comp k b a H1 H2 (FreeSig_boundary k a b H1 H2 H3))) as Hwf.
    destruct a as [ta da pa], b as [tb db pb]; simpl in *. subst db.
    destruct da as [|da]; [lia|].
    unfold FreeCell_eq; simpl. apply (IC8 tb ta k (S da)); [exact Hwf | lia].
  - (* assoc: IC9 *) wf_of_goal. unfold FreeCell_eq; simpl.
    apply (IC9 _ _ _ k (cell_dim a)); assumption.
  - (* exchange: IC10 *) wf_of_goal. unfold FreeCell_eq; simpl.
    apply (IC10 _ _ _ _ m n (cell_dim x)); assumption.
  - (* unit r: IC11 *) wf_of_goal. unfold FreeCell_eq; simpl.
    set (c := cell_dim a - k) in *.
    destruct (Free_iter_src_proj c a ltac:(unfold c; lia)) as [Hs Hsd].
    destruct (Free_iter_id_proj c (Nat.iter c Free_src a)) as [Hi Hid].
    rewrite Hi, Hs in HL |- *.
    apply (IC11 (cell_term a) k (cell_dim a) (cell_proof a)); [lia | exact HL].
  - (* unit l: IC12 *) wf_of_goal. unfold FreeCell_eq; simpl.
    set (c := cell_dim a - k) in *.
    destruct (Free_iter_tgt_proj c a ltac:(unfold c; lia)) as [Ht Htd].
    destruct (Free_iter_id_proj c (Nat.iter c Free_tgt a)) as [Hi Hid].
    assert (Hdim : cell_dim (Nat.iter c Free_id (Nat.iter c Free_tgt a)) = cell_dim a)
      by (rewrite Hid, Htd; unfold c; lia).
    rewrite Hi, Ht in HL |- *. rewrite Hdim in HL.
    apply (IC12 (cell_term a) k (cell_dim a) (cell_proof a)); [lia | exact HL].
  - (* id comp: IC13 *) wf_of_goal. unfold FreeCell_eq; simpl.
    inversion HL; subst.
    apply (IC13 _ _ k (cell_dim a)); [assumption | lia].
Qed.

End AdequacyF.
