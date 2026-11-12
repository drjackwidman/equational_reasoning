(** * Inverse.v
    Inverses and (∞,1)-categories (Sections 2.3 and 2.4 of the paper), over
    a model of EqCat∞ ([OmegaSig] with [IsEqCatModel], see [Adequacy.v]).

    Contents:
      - [is_inverse k f g]: g is a two-sided inverse of the (k+1)-cell f
        for composition along its k-dimensional boundary;
      - [inverse_unique]: two-sided inverses are unique;
      - [HasInverses lo inv]: an inverse operator on cells of dimension
        at least [lo], with the three rules of Section 2.3;
        [IsInfty1Cat] is the case lo = 2;
      - [inv_involutive]: the derived rule (f^-1)^-1 = f;
      - [fun_inverse]: functors preserve inverses.

    On the threshold: the text of Section 2.3 asks for inverses of n-cells
    with n >= 2, while the operator there is typed on every C_{n+1}, that
    is, on all cells of dimension >= 1. The threshold is a parameter here;
    every result holds for any value of it. *)

Require Import Arith PeanoNat Lia.
Require Import Syntax Axioms Meta NormalForm Model FreeModel Decidable Reflect Adequacy.
Require Import Functor.

Section Inverses.
Context (Sg : OmegaSig) (M : IsEqCatModel Sg).

(** g is a two-sided inverse of f, where f has dimension k+1:
    g : tgt f -> src f, g ∘_k f = id (src f), f ∘_k g = id (tgt f). *)
Definition is_inverse (k : nat) (f g : Cell Sg) : Prop :=
  cdim g = S k /\
  ceq (csrc g) (ctgt f) /\
  ceq (ctgt g) (csrc f) /\
  (forall H1 H2 H3, ceq (ccomp k g f H1 H2 H3) (cid (csrc f))) /\
  (forall H1 H2 H3, ceq (ccomp k f g H1 H2 H3) (cid (ctgt f))).

(** Both composites in [is_inverse] exist. *)
Lemma inverse_composable : forall k (f g : Cell Sg),
  cdim f = S k -> cdim g = S k ->
  ceq (csrc g) (ctgt f) -> ceq (ctgt g) (csrc f) ->
  (cdim g = cdim f /\ k < cdim g /\
   ceq (Nat.iter (cdim g - k) csrc g) (Nat.iter (cdim g - k) ctgt f))
  /\
  (cdim f = cdim g /\ k < cdim f /\
   ceq (Nat.iter (cdim f - k) csrc f) (Nat.iter (cdim f - k) ctgt g)).
Proof.
  intros k f g Hf Hg Hs Ht. split.
  - apply (comp1_ok Sg k g f Hg Hf Hs).
  - apply (comp1_ok Sg k f g Hf Hg). apply (ceq_sym Sg M). exact Ht.
Qed.

(** Two-sided inverses are unique:
    g = g ∘ id = g ∘ (f ∘ g') = (g ∘ f) ∘ g' = id ∘ g' = g'. *)
Theorem inverse_unique : forall k (f g g' : Cell Sg),
  cdim f = S k -> is_inverse k f g -> is_inverse k f g' -> ceq g g'.
Proof.
  intros k f g g' Hf (Hg & Hgs & Hgt & Hgf & Hfg) (Hg' & Hgs' & Hgt' & Hgf' & Hfg').
  pose (sy := ceq_sym Sg M). pose (tr := ceq_trans Sg M). pose (rf := ceq_refl Sg M).
  (* f ∘ g' *)
  destruct (comp1_ok Sg k f g' Hf Hg' (sy _ _ Hgt')) as (A1 & A2 & A3).
  set (fg' := ccomp k f g' A1 A2 A3).
  assert (Dfg' : cdim fg' = S k) by (unfold fg'; rewrite (cdim_comp Sg M); exact Hf).
  assert (Tfg' : ceq (ctgt fg') (ctgt f)) by (apply (tgt_comp_top Sg M); exact Hf).
  (* g ∘ (f ∘ g') *)
  destruct (comp1_ok Sg k g fg' Hg Dfg' (tr _ _ _ Hgs (sy _ _ Tfg'))) as (B1 & B2 & B3).
  (* g ∘ f *)
  destruct (comp1_ok Sg k g f Hg Hf Hgs) as (C1 & C2 & C3).
  set (gf := ccomp k g f C1 C2 C3).
  assert (Dgf : cdim gf = S k) by (unfold gf; rewrite (cdim_comp Sg M); exact Hg).
  assert (Sgf : ceq (csrc gf) (csrc f)) by (apply (src_comp_top Sg M); exact Hg).
  (* (g ∘ f) ∘ g' *)
  destruct (comp1_ok Sg k gf g' Dgf Hg' (tr _ _ _ Sgf (sy _ _ Hgt'))) as (E1 & E2 & E3).
  (* g ∘ id (tgt f) *)
  destruct (comp1_ok Sg k g (cid (ctgt f)) Hg (cdim_id_tgt Sg M k f Hf)
              (tr _ _ _ Hgs (sy _ _ (tgt_id Sg M (ctgt f))))) as (U1 & U2 & U3).
  (* id (src f) ∘ g' *)
  destruct (comp1_ok Sg k (cid (csrc f)) g' (cdim_id_src Sg M k f Hf) Hg'
              (tr _ _ _ (src_id Sg M (csrc f)) (sy _ _ Hgt'))) as (V1 & V2 & V3).
  apply (tr _ (ccomp k g (cid (ctgt f)) U1 U2 U3) _).
  { apply sy. apply (unit_r1' Sg M k g (ctgt f) Hg). apply sy. exact Hgs. }
  apply (tr _ (ccomp k g fg' B1 B2 B3) _).
  { apply (ccomp_ceq Sg M); [apply rf | apply sy; apply Hfg']. }
  apply (tr _ (ccomp k gf g' E1 E2 E3) _).
  { apply sy. apply (assoc Sg M). }
  apply (tr _ (ccomp k (cid (csrc f)) g' V1 V2 V3) _).
  { apply (ccomp_ceq Sg M); [apply Hgf | apply rf]. }
  apply (unit_l1' Sg M k g' (csrc f) Hg'). apply sy. exact Hgt'.
Qed.

(** Being inverse is symmetric: if g is an inverse of f then f is an
    inverse of g. *)
Lemma is_inverse_sym : forall k (f g : Cell Sg),
  cdim f = S k -> is_inverse k f g -> is_inverse k g f.
Proof.
  intros k f g Hf (Hg & Hgs & Hgt & Hgf & Hfg).
  split; [exact Hf | split; [| split; [| split]]].
  - apply (ceq_sym Sg M). exact Hgt.
  - apply (ceq_sym Sg M). exact Hgs.
  - intros H1 H2 H3. apply (ceq_trans Sg M _ (cid (ctgt f)) _); [apply Hfg |].
    apply (cid_ceq Sg M). apply (ceq_sym Sg M). exact Hgs.
  - intros H1 H2 H3. apply (ceq_trans Sg M _ (cid (csrc f)) _); [apply Hgf |].
    apply (cid_ceq Sg M). apply (ceq_sym Sg M). exact Hgt.
Qed.

(** An inverse operator on the cells of dimension at least [lo]: the three
    rules of Section 2.3, f^-1 : b -> a, f^-1 ∘ f = id a, f ∘ f^-1 = id b
    for f : a -> b. *)
Record HasInverses (lo : nat) (inv : Cell Sg -> Cell Sg) : Prop := {
  inv_ceq  : forall a b : Cell Sg, cdim a >= lo -> ceq a b -> ceq (inv a) (inv b);
  inv_spec : forall (k : nat) (f : Cell Sg),
      cdim f = S k -> S k >= lo -> is_inverse k f (inv f)
}.

(** An (∞,1)-category: every cell of dimension at least 2 is invertible. *)
Definition IsInfty1Cat (inv : Cell Sg -> Cell Sg) : Prop := HasInverses 2 inv.

(** The derived rule (f^-1)^-1 = f. *)
Theorem inv_involutive : forall lo inv, HasInverses lo inv ->
  forall (k : nat) (f : Cell Sg), cdim f = S k -> S k >= lo ->
  ceq (inv (inv f)) f.
Proof.
  intros lo inv HI k f Hf Hlo.
  pose proof (inv_spec lo inv HI k f Hf Hlo) as I1.
  assert (Di : cdim (inv f) = S k) by (destruct I1 as (H & _); exact H).
  pose proof (inv_spec lo inv HI k (inv f) Di Hlo) as I2.
  apply (inverse_unique k (inv f) (inv (inv f)) f Di I2).
  apply is_inverse_sym; assumption.
Qed.

End Inverses.

(** Functors preserve inverses: F (f^-1) = (F f)^-1. *)
Section FunctorInverse.
Context (C D : OmegaSig) (MC : IsEqCatModel C) (MD : IsEqCatModel D).
Context (F : Cell C -> Cell D) (HF : IsFunctor C D F).

(** A functor sends an inverse of f to an inverse of F f. *)
Lemma fun_is_inverse : forall k (f g : Cell C),
  cdim f = S k -> is_inverse C k f g -> is_inverse D k (F f) (F g).
Proof.
  intros k f g Hf (Hg & Hgs & Hgt & Hgf & Hfg).
  pose (sy := ceq_sym D MD). pose (tr := ceq_trans D MD).
  destruct (inverse_composable C MC k f g Hf Hg Hgs Hgt) as ((P1 & P2 & P3) & (Q1 & Q2 & Q3)).
  split; [rewrite (fun_dim C D F HF); exact Hg | split; [| split; [| split]]].
  - apply (tr _ (F (csrc g)) _); [apply (fun_src C D F HF); lia |].
    apply (tr _ (F (ctgt f)) _); [apply (fun_ceq C D F HF); exact Hgs |].
    apply sy. apply (fun_tgt C D F HF). lia.
  - apply (tr _ (F (ctgt g)) _); [apply (fun_tgt C D F HF); lia |].
    apply (tr _ (F (csrc f)) _); [apply (fun_ceq C D F HF); exact Hgt |].
    apply sy. apply (fun_src C D F HF). lia.
  - intros H1 H2 H3.
    apply (tr _ (F (ccomp k g f P1 P2 P3)) _); [apply sy; apply (fun_comp C D F HF) |].
    apply (tr _ (F (cid (csrc f))) _); [apply (fun_ceq C D F HF); apply Hgf |].
    apply (tr _ (cid (F (csrc f))) _); [apply (fun_id C D F HF) |].
    apply (cid_ceq D MD). apply sy. apply (fun_src C D F HF). lia.
  - intros H1 H2 H3.
    apply (tr _ (F (ccomp k f g Q1 Q2 Q3)) _); [apply sy; apply (fun_comp C D F HF) |].
    apply (tr _ (F (cid (ctgt f))) _); [apply (fun_ceq C D F HF); apply Hfg |].
    apply (tr _ (cid (F (ctgt f))) _); [apply (fun_id C D F HF) |].
    apply (cid_ceq D MD). apply sy. apply (fun_tgt C D F HF). lia.
Qed.

Theorem fun_inverse : forall lo invC invD,
  HasInverses C lo invC -> HasInverses D lo invD ->
  forall (k : nat) (f : Cell C), cdim f = S k -> S k >= lo ->
  ceq (F (invC f)) (invD (F f)).
Proof.
  intros lo invC invD HC HD k f Hf Hlo.
  assert (DF : cdim (F f) = S k) by (rewrite (fun_dim C D F HF); exact Hf).
  apply (inverse_unique D MD k (F f) (F (invC f)) (invD (F f)) DF).
  - apply fun_is_inverse; [exact Hf | apply (inv_spec C lo invC HC); assumption].
  - apply (inv_spec D lo invD HD); assumption.
Qed.

End FunctorInverse.

Print Assumptions inverse_unique.
Print Assumptions inv_involutive.
Print Assumptions fun_inverse.
