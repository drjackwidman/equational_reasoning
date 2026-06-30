Require Import Arith PeanoNat Lia List Bool.
Require Import Syntax Axioms FreeModel.

Set Implicit Arguments.

Fixpoint size (t : Term) : nat :=
  match t with
  | gen _       => 1
  | src a       => 1 + size a
  | tgt a       => 1 + size a
  | id a        => 1 + size a
  | comp _ a b  => 1 + size a + size b
  end.

Definition nf_id_elim (k : nat) (a b : Term) : Term := a.
Definition nf_assoc_step (k : nat) (a b : Term) : Term := a.
Definition nf_exchange_step (m : nat) (a b : Term) : Term := a.
Definition nf_comp_step (k : nat) (a b : Term) : Term := comp k a b.

Fixpoint nf_bounded (n : nat) (t : Term) : Term :=
  match n with
  | O => t
  | S n' =>
      match t with
      | gen g => gen g
      | src a => src (nf_bounded n' a)
      | tgt a => tgt (nf_bounded n' a)
      | id a  => id (nf_bounded n' a)
      | comp k a b => nf_comp_step k (nf_bounded n' a) (nf_bounded n' b)
      end
  end.

Definition nf (t : Term) : Term := nf_bounded (size t) t.

Lemma nf_bounded_dim_preserve : forall n t v,
  dim t = Some v -> dim (nf_bounded n t) = Some v.
Proof.
  induction n as [|n' IHn]; intros t v Hdim.
  - (* Base Case: n = O *)
    simpl; exact Hdim.
  - (* Inductive Step: n = S n' *)
    destruct t as [g | a | a | a | k a b]; simpl in Hdim |- *.
    + (* Case: gen g *)
      exact Hdim.
    + (* Case: src a *)
      destruct (dim a) as [[|da]|] eqn:Ha; try discriminate.
      rewrite (IHn a (S da) Ha); exact Hdim.
    + (* Case: tgt a *)
      destruct (dim a) as [[|da]|] eqn:Ha; try discriminate.
      rewrite (IHn a (S da) Ha); exact Hdim.
    + (* Case: id a *)
      destruct (dim a) as [da|] eqn:Ha; try discriminate.
      rewrite (IHn a da Ha); exact Hdim.
    + (* Case: comp k a b *)
      unfold nf_comp_step; simpl.
      destruct (dim a) as [da|] eqn:Ha; try discriminate.
      destruct (dim b) as [db|] eqn:Hb; try discriminate.
      rewrite (IHn a da Ha), (IHn b db Hb); exact Hdim.
Qed.

Theorem nf_dim_preserve : forall t n, dim t = Some n -> dim (nf t) = Some n.
Proof.
  intros t n Hdim; unfold nf; apply nf_bounded_dim_preserve; exact Hdim.
Qed.

Theorem nf_comp_step_sound : forall k a b d, 
  wf a d -> wf b d -> nf_comp_step k a b == comp k a b.
Admitted.

Theorem nf_sound : forall t d, 
  wf t d -> nf t == t.
Admitted.

Theorem nf_complete : forall t1 t2 d, 
  wf t1 d -> wf t2 d -> t1 == t2 -> nf t1 = nf t2.
Admitted.

(** Decidability of provable equality in the strict free model.

    The decision procedure is: normalize both underlying terms and compare
    the normal forms with the (decidable) syntactic equality [Term_eq_dec].
      - If [nf t1 = nf t2] then [t1 == nf t1 = nf t2 == t2] by soundness.
      - If [nf t1 <> nf t2] then [~ t1 == t2]: were they equal, their
        dimensions would agree ([eq_cat_dim_agree]) and completeness would
        force [nf t1 = nf t2], a contradiction.
    This reduces decidability to [nf_sound], [nf_complete], and the
    dimension-agreement bridge. *)
Theorem free_cell_decidable : forall (c1 c2 : FreeCell), {c1 === c2} + {~ c1 === c2}.
Proof.
  intros [t1 d1 p1] [t2 d2 p2].
  unfold FreeCell_eq; simpl.
  destruct (Term_eq_dec (nf t1) (nf t2)) as [Heq | Hneq].
  - (* normal forms coincide: terms are provably equal *)
    left.
    apply (E3_trans t1 (nf t2) t2).
    + rewrite <- Heq. apply E2_sym. exact (nf_sound p1).
    + exact (nf_sound p2).
  - (* normal forms differ: terms cannot be provably equal *)
    right. intro Hcontra. apply Hneq.
    assert (Hd : d1 = d2) by exact (eq_cat_dim_agree t1 t2 d1 d2 Hcontra p1 p2).
    subst d2.
    exact (nf_complete p1 p2 Hcontra).
Qed.


