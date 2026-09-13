(** * Examples.v
    The recurring obligations, each closed by one tactic call.

    The blurb names four kinds of obligation:
      (1) boundary matching,
      (2) repeated source and target simplification,
      (3) identity propagation,
      (4) equality of closed terms in the free setting.
    Below, one section per kind, on a small concrete generating set.
    Every goal is closed by [eqcat_wf], [eqcat_decide] or [eqcat_refute],
    except the two ill-formedness checks, which are closed by computation. *)

Require Import Syntax Adequacy.

(** ** The generating data: a stratified set with one cell in each of
    dimensions 0..3. Boundaries of generators are fresh (the free model
    assumes no compatibilities between generators, cf. §4 of the paper). *)
Module Gen <: GEN.
  Inductive G := x | f | alpha | beta.
  Definition Generator := G.
  Definition gen_dim (g : G) : nat :=
    match g with x => 0 | f => 1 | alpha => 2 | beta => 3 end.
  Definition Generator_eq_dec : forall g1 g2 : Generator, {g1 = g2} + {g1 <> g2}.
  Proof. decide equality. Defined.
End Gen.

Module E := AdequacyF Gen.
Import E.

Notation x     := (gen Gen.x).
Notation f     := (gen Gen.f).
Notation alpha := (gen Gen.alpha).
Notation beta  := (gen Gen.beta).

(** ---------------------------------------------------------------- *)
(** ** (1) Boundary matching.
    Well-formedness of a composite requires  src^{n-k} a == tgt^{n-k} b.
    [wf] is a [Prop] with an [eq_cat] premise; [eqcat_wf] discharges it
    by normalizing both boundaries. *)

(** Vertical unit composite on a 2-cell: id_{tgt α} ∘₁ α. *)
Example bm_unit2 : wf (comp 1 (id (tgt alpha)) alpha) 2.
Proof. eqcat_wf. Qed.

(** A 3-cell against a doubly-identity-extended boundary, along ∘₁.
    The check must simplify  src² (id² tgt² β)  down to  tgt² β. *)
Example bm_codim2 : wf (comp 1 (id (id (tgt (tgt beta)))) beta) 3.
Proof. eqcat_wf. Qed.

(** Along ∘₀: three identities, three sources. *)
Example bm_codim3 : wf (comp 0 beta (id (id (id (src (src (src beta))))))) 3.
Proof. eqcat_wf. Qed.

(** A nested composite: both inner and outer boundaries are checked. *)
Example bm_nested :
  wf (comp 1 (comp 1 (id (tgt alpha)) alpha) (id (src alpha))) 2.
Proof. eqcat_wf. Qed.

(** Ill-formed: a generator against itself. In the free model
    src α ≠ tgt α, so α ∘₁ α does not exist. The checker returns [None]. *)
Example bm_fail : wfb (comp 1 alpha alpha) = None.
Proof. vm_compute. reflexivity. Qed.

(** Ill-formed: dimension mismatch. *)
Example bm_fail_dim : wfb (comp 0 alpha f) = None.
Proof. vm_compute. reflexivity. Qed.

(** ---------------------------------------------------------------- *)
(** ** (2) Repeated source and target simplification.
    Chains of src/tgt/id collapse to a single end-block (rules R6–R9,
    axioms IC1–IC4). *)

(** Globularity: src src = src tgt, tgt src = tgt tgt. *)
Example st_glob1 : src (src beta) == src (tgt beta).
Proof. eqcat_decide. Qed.

Example st_glob2 : tgt (src (tgt beta)) == tgt (tgt (src beta)).
Proof. eqcat_decide. Qed.

(** Mixed chains reduce to a pure src- or tgt-block. *)
Example st_mixed : src (tgt (src beta)) == src (src (src beta)).
Proof. eqcat_decide. Qed.

(** src/tgt strip identities. *)
Example st_strip : src (tgt (id (id alpha))) == alpha.
Proof. eqcat_decide. Qed.

(** src of a composite is src of the right operand (IC5). *)
Example st_comp : src (comp 1 (id (tgt alpha)) alpha) == src alpha.
Proof. eqcat_decide. Qed.

(** src of a ∘₀-composite of 2-cells distributes (IC7), then collapses. *)
Example st_distrib :
  src (comp 0 alpha (id (id (src (src alpha))))) == src alpha.
Proof. eqcat_decide. Qed.

(** Not equal: the two 0-cell boundaries of a 2-cell differ. *)
Example st_neq : ~ (src (src alpha) == tgt (tgt alpha)).
Proof. eqcat_refute. Qed.

(** ---------------------------------------------------------------- *)
(** ** (3) Identity propagation.
    Unit laws (IC11/IC12), id of a composite (IC13), ids through
    src/tgt (IC3/IC4). *)

(** Left and right unit laws for vertical composition. *)
Example id_lunit : comp 1 (id (tgt alpha)) alpha == alpha.
Proof. eqcat_decide. Qed.

Example id_runit : comp 1 alpha (id (src alpha)) == alpha.
Proof. eqcat_decide. Qed.

(** Unit laws at codimension 2 (horizontal composition of 2-cells). *)
Example id_lunit0 : comp 0 (id (id (tgt (tgt alpha)))) alpha == alpha.
Proof. eqcat_decide. Qed.

Example id_runit0 : comp 0 alpha (id (id (src (src alpha)))) == alpha.
Proof. eqcat_decide. Qed.

(** id distributes over composition (IC13). *)
Example id_comp :
  id (comp 1 (id (tgt alpha)) alpha) == comp 1 (id (id (tgt alpha))) (id alpha).
Proof. eqcat_decide. Qed.

(** Identity cells are absorbed on both sides at once. *)
Example id_both :
  comp 1 (id (tgt alpha)) (comp 1 alpha (id (src alpha))) == alpha.
Proof. eqcat_decide. Qed.

(** Iterated identities on a 0-cell compose to themselves. *)
Example id_iter : comp 0 (id (id x)) (id (id x)) == id (id x).
Proof. eqcat_decide. Qed.

(** ---------------------------------------------------------------- *)
(** ** (4) Equality of closed terms in the free setting.
    Larger terms mixing all of the above. *)

(** Example 4.3 from the paper, with dim a = 3:
      u = id² tgt² a,  v = id² tgt src a,  E = (id² tgt² (u ∘₁ v)) ∘₁ u,
    and NF(E) = u. *)
Definition u := id (id (tgt (tgt beta))).
Definition v := id (id (tgt (src beta))).
Definition Ex43 := comp 1 (id (id (tgt (tgt (comp 1 u v))))) u.

Example paper_4_3 : Ex43 == u.
Proof. eqcat_decide. Qed.

Example paper_4_3_wf : wf Ex43 3.
Proof. eqcat_wf. Qed.

(** Associativity instance (IC9) with identity operands. *)
Example assoc :
  comp 1 (comp 1 (id (tgt alpha)) alpha) (id (src alpha))
  == comp 1 (id (tgt alpha)) (comp 1 alpha (id (src alpha))).
Proof. eqcat_decide. Qed.

(** Exchange instance (IC10) between ∘₀ and ∘₁ on 2-cells:
      (x ∘₁ y) ∘₀ (z ∘₁ w) == (x ∘₀ z) ∘₁ (y ∘₀ w)
    with x = α, y = id src α, z = w = id² src² α. Both sides reduce to α. *)
Definition z := id (id (src (src alpha))).
Example exchange :
  comp 0 (comp 1 alpha (id (src alpha))) (comp 1 z z)
  == comp 1 (comp 0 alpha z) (comp 0 (id (src alpha)) z).
Proof. eqcat_decide. Qed.

(** Both sides of the exchange are well-formed 2-cells. *)
Example exchange_wf_l : wf (comp 0 (comp 1 alpha (id (src alpha))) (comp 1 z z)) 2.
Proof. eqcat_wf. Qed.

Example exchange_wf_r : wf (comp 1 (comp 0 alpha z) (comp 0 (id (src alpha)) z)) 2.
Proof. eqcat_wf. Qed.

(** Refutation: a genuine generator is not its own identity extension. *)
Example neq_id : ~ (id (tgt alpha) == alpha).
Proof. eqcat_refute. Qed.

(** The Lemma 4.4 counterexample from [lemma_4_4_counterexample.txt]:
    the paper's case (b) would return the LEFT operand id_g; the correct
    value is the RIGHT operand α, and the two are distinct. *)
Example lemma44_correct_value : comp 1 (id (tgt alpha)) alpha == alpha.
Proof. eqcat_decide. Qed.

Example lemma44_wrong_value : ~ (comp 1 (id (tgt alpha)) alpha == id (tgt alpha)).
Proof. eqcat_refute. Qed.

(** ---------------------------------------------------------------- *)
(** ** At the level of the free model: [FreeCell] equality. *)

Definition c1 : FreeCell := ltac:(mkcell constr:(comp 1 (id (tgt alpha)) alpha) constr:(2)).
Definition c2 : FreeCell := ltac:(mkcell constr:(alpha) constr:(2)).

Example freecell_eq : c1 === c2.
Proof. eqcat_decide. Qed.

(** And the original sumbool decision, evaluated: it picks [left]. *)
Example freecell_dec_left :
  (if free_cell_decidable c1 c2 then true else false) = true.
Proof. vm_compute. reflexivity. Qed.

(** ---------------------------------------------------------------- *)
(** ** Audit. Everything above is closed under the global context: the
    only parameters were the generators, and they are now concrete. *)
Print Assumptions paper_4_3.
Print Assumptions exchange.
Print Assumptions freecell_eq.

(** The free model on this generating set satisfies all laws of Figure 2, closed. *)
Print Assumptions FreeModel_is_EqCat_model.
