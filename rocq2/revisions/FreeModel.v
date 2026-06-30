(** * FreeModel.v
    Formalization of the Free Model in the Strict Case for EqCat∞.
    Reference: "Equational Reasoning in ∞-Categories"

    In the strict case, the free model is constructed by quotienting 
    the well-formed raw terms by the provable equational theory [eq_cat]. *)

Require Import Arith Lia.
Require Import Setoid Morphisms.
Require Import Syntax Axioms Meta.

(** ** 1. Definitional Structure of Free Cells

    A cell in the free model bundles a raw [Term], an explicit dimension [n], 
    and a structural proof of the new inductive [wf] predicate at that dimension. *)

Record FreeCell : Type := {
  cell_term : Term;
  cell_dim  : nat;
  cell_proof : wf cell_term cell_dim
}.

(** ** 2. Equivalence Relation on FreeCell

    Two cells are equivalent if their underlying raw terms are provably equal 
    under the revised [eq_cat] relation (notation [==]). *)

Definition FreeCell_eq (c1 c2 : FreeCell) : Prop :=
  cell_term c1 == cell_term c2.

Infix "===" := FreeCell_eq (at level 70, no associativity).

(** We establish that [FreeCell_eq] is an equivalence relation using the 
    revised structural axioms [E1_refl], [E2_sym], and [E3_trans]. *)

Lemma FreeCell_eq_refl : forall c, c === c.
Proof.
  intros [t d p]; exact (E1_refl t).
Qed.

Lemma FreeCell_eq_sym : forall c1 c2, c1 === c2 -> c2 === c1.
Proof.
  intros [t1 d1 p1] [t2 d2 p2] H; exact (E2_sym t1 t2 H).
Qed.

Lemma FreeCell_eq_trans : forall c1 c2 c3, c1 === c2 -> c2 === c3 -> c1 === c3.
Proof.
  intros [t1 d1 p1] [t2 d2 p2] [t3 d3 p3] H1 H2; exact (E3_trans t1 t2 t3 H1 H2).
Qed.

(** Register [FreeCell] as a Setoid to unlock rewriting automation within Rocq. *)
Add Parametric Relation : FreeCell FreeCell_eq
  reflexivity proved by FreeCell_eq_refl
  symmetry proved by FreeCell_eq_sym
  transitivity proved by FreeCell_eq_trans
  as FreeCell_setoid.

(** ** 3. Operational Signatures on the Quotient

    We lift [src], [tgt], and [id] to map over [FreeCell]. 
    For 0-cells, totalization maps the cell to itself to preserve typing constraints. *)

Definition Free_src (c : FreeCell) : FreeCell.
Proof.
  destruct c as [t d p].
  destruct d.
  - (* Totalization boundary for 0-cells: map to itself to preserve type witness 'p' *)
    exact {| cell_term := t; cell_dim := 0; cell_proof := p |}.
  - (* For an (S d) cell, [wf_src] explicitly proves that [src t] is a d-cell *)
    exact {| cell_term := src t; cell_dim := d; cell_proof := wf_src t d p |}.
Defined.

Definition Free_tgt (c : FreeCell) : FreeCell.
Proof.
  destruct c as [t d p].
  destruct d.
  - (* Totalization boundary for 0-cells *)
    exact {| cell_term := t; cell_dim := 0; cell_proof := p |}.
  - (* For an (S d) cell, [wf_tgt] explicitly proves that [tgt t] is a d-cell *)
    exact {| cell_term := tgt t; cell_dim := d; cell_proof := wf_tgt t d p |}.
Defined.

Definition Free_id (c : FreeCell) : FreeCell.
Proof.
  destruct c as [t d p].
  (* Maps an n-cell to an (S n)-cell cleanly using the [wf_id] constructor *)
  exact {| cell_term := id t; cell_dim := S d; cell_proof := wf_id t d p |}.
Defined.

(** ** 4. Metatheoretical Dimension Invariance Lemma

    We assert that provable equality preserves the inductive typing dimensions. 
    This acts as our translation bridge for dependent types. *)
Lemma eq_cat_dim_agree : forall t1 t2 d1 d2,
  t1 == t2 -> wf t1 d1 -> wf t2 d2 -> d1 = d2.
Proof.
  exact Meta.eq_cat_dim_agree.
Qed.

(** ** 5. Morphism Adequacy Proofs

    We declare parametric morphisms to guarantee that the structural 
    operators cleanly respect the Setoid equivalence relation. *)

Add Parametric Morphism : Free_src
  with signature FreeCell_eq ==> FreeCell_eq as Free_src_morph.
Proof.
  intros [t1 d1 p1] [t2 d2 p2] Heq.
  simpl in *.
  unfold FreeCell_eq in Heq.
  (* Step 1: Force dimensions to agree using our metatheory bridge *)
  assert (Hdim: d1 = d2) by exact (eq_cat_dim_agree t1 t2 d1 d2 Heq p1 p2).
  subst d2.
  (* Step 2: Now destructing d1 handles both sides symmetrically *)
  destruct d1.
  - (* Both are 0-cells *)
    exact Heq.
  - (* Both are (S d1) cells; types match perfectly now *)
    exact (E5_src t1 t2 d1 Heq p1 p2).
Qed.

Add Parametric Morphism : Free_tgt
  with signature FreeCell_eq ==> FreeCell_eq as Free_tgt_morph.
Proof.
  intros [t1 d1 p1] [t2 d2 p2] Heq.
  simpl in *.
  unfold FreeCell_eq in Heq.
  assert (Hdim: d1 = d2) by exact (eq_cat_dim_agree t1 t2 d1 d2 Heq p1 p2).
  subst d2.
  destruct d1.
  - exact Heq.
  - exact (E6_tgt t1 t2 d1 Heq p1 p2).
Qed.

Add Parametric Morphism : Free_id
  with signature FreeCell_eq ==> FreeCell_eq as Free_id_morph.
Proof.
  intros [t1 d1 p1] [t2 d2 p2] Heq.
  simpl in *.
  exact (E8_id t1 t2 Heq).
Qed.

(** ** 6. Composition under the Mutual Architecture

    To compose [b] and [a] along dimension [k] inside our strict free model, 
    the boundaries must cleanly match. In the revised framework, this proof 
    is embedded directly into the [wf_comp] constructor of the typing relation. *)

Definition Free_comp (k : nat) (b a : FreeCell)
  (Hdim : cell_dim a = cell_dim b)
  (Hk : k < cell_dim a)
  (Hglue : iter_src (cell_dim a - k) (cell_term a) == iter_tgt (cell_dim a - k) (cell_term b)) : FreeCell.
Proof.
  destruct a as [ta da pa].
  destruct b as [tb db pb].
  simpl in *.
  subst db.
  exact {| cell_term := comp k ta tb; 
           cell_dim  := da; 
           cell_proof := wf_comp k ta tb da pa pb Hk Hglue |}.
Defined.
