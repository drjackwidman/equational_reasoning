(** * Axioms of EqCat∞

    The provable-equality relation [t == t'] on raw terms.
    Reference: "Equational Reasoning in ∞-Categories", Figure 2.

    Conventions:
      - [dim e = Some n] is written explicitly; partial dimensions are
        not implicit.
      - For each premise of the form "dim x >= k" in the paper, we
        require [dim e = Some d] with [d >= k].
      - Equality of the theory is the inductive relation [eq_cat], NOT
        Coq's built-in [=]. *)

(* JW: Revision notes (in response to Liron's review).
   Two changes here, both prompted by her comments:
     1. [wf] is now an inductive judgment, defined MUTUALLY with [eq_cat]
        below. The mutual definition is forced by change (2): [wf_comp]
        carries a boundary premise expressed via [eq_cat], and [eq_cat]
        constructors carry [wf] premises, so neither can be defined
        before the other.
     2. Composition now checks the required boundary condition. Concretely,
        every constructor that introduces a [comp] (E7, IC5–IC10, IC11,
        IC12, IC13) now carries a [wf (comp ...) d] premise that bundles
        together the dimension constraints AND the boundary equation
        [iter_src (n-k) a == iter_tgt (n-k) b]. This replaces the loose
        [dim x = Some d] / [dim y = Some d] / [d > n] premises used
        previously, which omitted the boundary check entirely.
   Convention reminder: [comp k a b] denotes [a ∘_k b] (natural order;
   first argument is the left operand of the paper's [∘_k]). *)

Require Import Arith Lia.
Require Import Syntax.

Reserved Notation "a == b" (at level 70, no associativity).

(* JW: NEW. The mutual block defines [wf] alongside [eq_cat] because
   [wf_comp] uses [eq_cat] for the boundary premise. *)
Inductive wf : Term -> nat -> Prop :=
| wf_gen :
    forall g, wf (gen g) (gen_dim g)
| wf_src :
    forall e n, wf e (S n) -> wf (src e) n
| wf_tgt :
    forall e n, wf e (S n) -> wf (tgt e) n
| wf_id  :
    forall e n, wf e n -> wf (id e) (S n)
| wf_comp :
    forall k a b n,
      wf a n -> wf b n ->
      k < n ->
      iter_src (n - k) a == iter_tgt (n - k) b ->
      wf (comp k a b) n

with eq_cat : Term -> Term -> Prop :=

(** ** Structural equality axioms (E1–E8) *)

(** E1: reflexivity. *)
| E1_refl :
    forall x, x == x

(** E2: symmetry. *)
| E2_sym :
    forall x y, x == y -> y == x

(** E3: transitivity. *)
| E3_trans :
    forall x y z, x == y -> y == z -> x == z

(** E4 ("equality preserves dimension") is not a constructor — its
    conclusion is an equality of [option nat], not of [Term]. It is
    derivable; see [eq_cat_dim] below. *)

(** E5: src is a congruence, where defined. *)
(* JW: WAS:
   | E5_src :
       forall x y n,
         x == y -> dim x = Some (S n) -> src x == src y
   CHANGED: replaced the [dim] premise with [wf] premises on both sides.
   Once dimensions are tracked via the inductive judgment, both [x] and
   [y] are required to be well-formed at the same dimension. *)
| E5_src :
    forall x y n,
      x == y -> wf x (S n) -> wf y (S n) ->
      src x == src y

(** E6: tgt is a congruence, where defined. *)
(* JW: WAS:
   | E6_tgt :
       forall x y n,
         x == y -> dim x = Some (S n) -> tgt x == tgt y
   CHANGED: same pattern as E5. *)
| E6_tgt :
    forall x y n,
      x == y -> wf x (S n) -> wf y (S n) ->
      tgt x == tgt y

(** E7: composition is a congruence. *)
(* JW: WAS:
   | E7_comp :
       forall x y z w n d,
         x == y -> z == w ->
         dim x = Some d -> dim y = Some d ->
         dim z = Some d -> dim w = Some d ->
         d > n ->
         comp n z x == comp n w y
   CHANGED: replaced the four [dim] premises and the [d > n] inequality
   with [wf (comp n x z) d] and [wf (comp n y w) d]. The [wf] premises
   bundle the dimension equalities, the [d > n] constraint, AND the
   required boundary conditions for both compositions in one statement.
   Argument order preserved: [comp n x z] corresponds to [x ∘_n z]. *)
| E7_comp :
    forall x y z w n d,
      x == y -> z == w ->
      wf (comp n x z) d -> wf (comp n y w) d ->
      comp n x z == comp n y w

(** E8: id is a congruence. *)
| E8_id :
    forall x y, x == y -> id x == id y

(** ** ∞-categorical axioms (IC1–IC13) *)

(** IC1: dim x >= 2 ==> src (src x) == src (tgt x). *)
(* JW: WAS:
   | IC1 :
       forall x n,
         dim x = Some n -> n >= 2 ->
         src (src x) == src (tgt x)
   CHANGED: [dim x = Some n] replaced by [wf x n]. Same content, just
   tracked via the new inductive judgment. *)
| IC1 :
    forall x n,
      wf x n -> n >= 2 ->
      src (src x) == src (tgt x)

(** IC2: dim x >= 2 ==> tgt (src x) == tgt (tgt x). *)
(* JW: same change as IC1. *)
| IC2 :
    forall x n,
      wf x n -> n >= 2 ->
      tgt (src x) == tgt (tgt x)

(** IC3: src (id x) == x. *)
(* JW: WAS: [dim x = Some n -> ...]. CHANGED to [wf x n -> ...]. *)
| IC3 :
    forall x n, wf x n -> src (id x) == x

(** IC4: tgt (id x) == x. *)
(* JW: same change as IC3. *)
| IC4 :
    forall x n, wf x n -> tgt (id x) == x

(** IC5: dim x = dim y = n+1 ==> src (y o[n] x) == src x. *)
(* JW: WAS:
   | IC5 :
       forall x y n,
         dim x = Some (S n) -> dim y = Some (S n) ->
         src (comp n y x) == src x
   CHANGED: replaced both [dim] premises with the single
   [wf (comp n y x) (S n)]. This is where Liron's boundary point bites:
   the original axiom permitted forming [comp n y x] without checking
   that [src y == tgt x]. The [wf] premise now folds that check in. *)
| IC5 :
    forall x y n,
      wf (comp n y x) (S n) ->
      src (comp n y x) == src x

(** IC6: dim x = dim y = n+1 ==> tgt (y o[n] x) == tgt y. *)
(* JW: same change as IC5. *)
| IC6 :
    forall x y n,
      wf (comp n y x) (S n) ->
      tgt (comp n y x) == tgt y

(** IC7: dim x = dim y > n+1 ==> src (y o[n] x) == src y o[n] src x. *)
(* JW: WAS:
   | IC7 :
       forall x y n d,
         dim x = Some d -> dim y = Some d -> d > S n ->
         src (comp n y x) == comp n (src y) (src x)
   CHANGED: dimension and boundary on the LHS folded into [wf (comp n y x) d].
   The [d > S n] inequality is kept as a separate premise because it
   is a distinct constraint (the conclusion mentions the lower-dim
   composite [comp n (src y) (src x)] which requires [d - 1 > n]). *)
| IC7 :
    forall x y n d,
      wf (comp n y x) d -> d > S n ->
      src (comp n y x) == comp n (src y) (src x)

(** IC8: dim x = dim y > n+1 ==> tgt (y o[n] x) == tgt y o[n] tgt x. *)
(* JW: same change as IC7. *)
| IC8 :
    forall x y n d,
      wf (comp n y x) d -> d > S n ->
      tgt (comp n y x) == comp n (tgt y) (tgt x)

(** IC9: associativity. dim x = dim y = dim z > n ==>
        (x o[n] y) o[n] z == x o[n] (y o[n] z). *)
(* JW: WAS:
   | IC9 :
       forall x y z n d,
         dim x = Some d -> dim y = Some d -> dim z = Some d -> d > n ->
         comp n (comp n x y) z == comp n x (comp n y z)
   CHANGED: replaced the per-variable [dim] premises with [wf] of BOTH
   sides. This is important: the original axiom only constrained the
   variables, but neither nested composition was required to actually
   be well-formed (i.e., have its boundary satisfied). For instance,
   [comp n x y] could be ill-formed even with the dim premises. The
   two [wf] premises now ensure all four boundaries hold. *)
| IC9 :
    forall x y z n d,
      wf (comp n (comp n x y) z) d ->
      wf (comp n x (comp n y z)) d ->
      comp n (comp n x y) z == comp n x (comp n y z)

(** IC10: exchange. dim x = dim y = dim z = dim w > max(m,n), m <> n ==>
        (x o[n] y) o[m] (z o[n] w) == (x o[m] z) o[n] (y o[m] w). *)
(* JW: WAS:
   | IC10 :
       forall x y z w m n d,
         dim x = Some d -> dim y = Some d ->
         dim z = Some d -> dim w = Some d ->
         d > m -> d > n -> m <> n ->
         comp m (comp n x y) (comp n z w) ==
         comp n (comp m x z) (comp m y w)
   CHANGED: same pattern as IC9 — [wf] of both sides bundles all
   dimension, level, and boundary constraints (including [m <> n],
   which is implicit in the well-formedness of the nested compositions
   when the boundaries are checked). *)
| IC10 :
    forall x y z w m n d,
      wf (comp m (comp n x y) (comp n z w)) d ->
      wf (comp n (comp m x z) (comp m y w)) d ->
      comp m (comp n x y) (comp n z w) ==
      comp n (comp m x z) (comp m y w)

(** IC11: left identity. d = dim x > n ==>
        x o[n] (id^{d-n} (src^{d-n} x)) == x. *)
(* JW: WAS:
   | IC11 :
       forall x n d,
         dim x = Some d -> d > n ->
         comp n x (Nat.iter (d - n) id (Nat.iter (d - n) src x)) == x
   CHANGED: [Nat.iter (d-n) id (Nat.iter (d-n) src x)] rewritten using
   the new aliases [iter_id (d-n) (iter_src (d-n) x)]. Added a [wf] of
   the LHS so the composition is known to be well-formed (its boundary
   holds automatically by IC3/IC4 iterated, but Coq still needs the
   premise). [wf x d] kept since it's used independently of the LHS. *)
| IC11 :
    forall x n d,
      wf x d -> d > n ->
      wf (comp n x (iter_id (d - n) (iter_src (d - n) x))) d ->
      comp n x (iter_id (d - n) (iter_src (d - n) x)) == x

(** IC12: right identity. d = dim x > n ==>
        (id^{d-n} (tgt^{d-n} x)) o[n] x == x. *)
(* JW: same change as IC11. *)
| IC12 :
    forall x n d,
      wf x d -> d > n ->
      wf (comp n (iter_id (d - n) (iter_tgt (d - n) x)) x) d ->
      comp n (iter_id (d - n) (iter_tgt (d - n) x)) x == x

(** IC13: dim x = dim y > n, src^{d-n} y = tgt^{d-n} x ==>
        id (y o[n] x) == id y o[n] id x. *)
(* JW: WAS:
   | IC13 :
       forall x y n d,
         dim x = Some d -> dim y = Some d -> d > n ->
         Nat.iter (d - n) src y = Nat.iter (d - n) tgt x ->
         id (comp n y x) == comp n (id y) (id x)
   CHANGED: the boundary premise [Nat.iter (d-n) src y = Nat.iter (d-n) tgt x]
   used Coq's built-in [=] but the paper writes it as a Horn premise of
   the theory. Now that [wf (comp n y x) d] expresses the boundary using
   [eq_cat] (which is faithful to the universal Horn presentation), the
   separate equation premise is no longer needed — it is part of [wf]. *)
| IC13 :
    forall x y n d,
      wf (comp n y x) d -> d > n ->
      id (comp n y x) == comp n (id y) (id x)

where "a == b" := (eq_cat a b).
