# Progress report — Rocq formalization of strict-case decidability

## Where it stands

The whole development compiles under Rocq 8.15 (six files in `_CoqProject`:
`Syntax`, `Axioms`, `Meta`, `NormalForm`, `FreeModel`, `Decidable`; the old
`Normalizer.v` is obsolete and dropped from the build). The headline theorem
`free_cell_decidable` — decidability of provable equality in the strict free
model — is **assembled but not yet a complete proof**: it carries a `Qed`, but it
is built from **five `Admitted` lemmas** in `Decidable.v` and therefore inherits
those assumptions. (Compilation succeeding does *not* mean everything is proved:
Coq accepts an `Admitted` lemma on faith. `Print Assumptions free_cell_decidable`
reports the five.)

In other words, the **decision procedure is fully implemented and its top-level
correctness argument is wired up**, but its correctness is established only
*modulo* those five lemmas: to decide `e₁ = e₂`, normalize both and compare normal
forms with decidable syntactic equality; agreement gives equality via soundness,
disagreement gives inequality via completeness plus dimension-agreement. What's
left is discharging the five admitted lemmas that make the normalizer provably
correct.

The five remaining `Admitted` lemmas (all in `Decidable.v`):

- `toTerm_inj` — Lemma 4.2: distinct canonical, well-formed normal forms denote
  distinct cells (the injectivity / confluence core).
- `nf_comp_glue` — the Lemma 4.4 combinatorial step (a matched boundary makes the
  composite degenerate and `nf_comp` succeed).
- `normalize_sound` — `normalize` is sound with respect to `==`.
- `src_pow_sound`, `tgt_pow_sound` — the NF-level iterated `src`/`tgt` operators
  agree with the term-level ones.

Note `normalize_total` and `normalize_complete` are now proved (`Qed`) — but, like
`free_cell_decidable`, conditionally on the five lemmas above.

## The normalizer is built (this is the new work)

I implemented §4 as a structurally-recursive `normalize : Term → option NF`,
where `NF` is a typed, canonical representation of the normal forms `id^ℓ end^m a`.
Rather than the paper's three-pass rewriting (push unary ops down, normalize unary
leaves, eliminate compositions bottom-up), I fold all of it into smart
constructors `nf_src`, `nf_tgt`, `nf_id`, `nf_comp` that realize rules R1–R11 and
Lemma 4.4 directly. This is obviously terminating (plain structural recursion) and
makes soundness/completeness reduce to induction on terms / on derivations.

## What's genuinely proven (all `Qed`, no holes)

- The unary fragment is fully sound — `nf_src`, `nf_tgt`, `nf_id` provably agree
  with the axioms (the src/tgt "winner" rules R8/R9 come out of IC1/IC2, the
  id-stripping rules R6/R7 from IC3/IC4).
- Normal forms are well-formed terms, with correct dimensions.
- A **retraction**: `normalize (toTerm u) = u`, i.e. every normal form
  round-trips. This is a strong sanity check that the normalizer and the `NF`
  representation actually line up.

## What remains (the deep half, currently admitted)

The five `Admitted` lemmas listed above. The central one is `normalize_sound`
(soundness of composition, Lemma 4.4), proved by a mutual induction over the
combined well-formedness/equality judgment, together with `toTerm_inj`,
`nf_comp_glue`, and the iterated-operator lemmas `src_pow_sound` / `tgt_pow_sound`.

For `normalize_sound` I've worked out the crux that avoids needing a separate
semantic model: the boundary condition sitting inside `wf_comp` is itself an
equality derivation, so its induction hypothesis hands you exactly the
normal-form-level equation you need to justify the composition collapse. The
hardest cases there are associativity (IC9) and exchange (IC10). (`normalize_complete`,
by contrast, is already discharged `Qed` — conditionally on these lemmas.)

---

## The bug I found in Lemma 4.4 (worth raising)

While implementing the composition constructor, I found that **Lemma 4.4, read
literally, returns the wrong operand on unit-absorption.** The lemma's three cases
say the composite `u ∘ v` of two normal forms equals `u` in cases (a)/(b) and `v`
in case (c), gated by conditions like `k ≤ ℓ`. When I tested those conditions
against concrete identity laws they came out backwards.

Concretely, take a 2-cell `α : f ⇒ g` and the identity `id_f` on its source. The
right-unit law gives `α ∘₁ id_f = α`. Here the left operand is `α` (no `id`s,
`ℓ = 0`) and we should return it. But the lemma's cases that return the left
operand all require `k ≤ ℓ` — here `k = 1`, `ℓ = 0`, so *none of them fire*, and
the only case that matches is the one returning the **other** operand `id_f`. The
symmetric left-unit example `id_g ∘₁ α = α` fails the same way: the matching case
returns the identity `id_g` instead of `α`. (The lemma's *typeability conditions*
are fine; it's the "= u" / "= v" verdicts that are swapped relative to which
operand is the genuine cell.) The paper's own running example `u ∘₁ u = u` happens
not to expose this because there both operands are equal.

### The fix

Instead of transcribing the (a)/(b)/(c) bookkeeping, I defined `nf_comp` straight
from the two unit laws it's supposed to encode:

- if the right operand equals the identity-extension of `src^c` of the left
  (this is exactly IC11), the composite is the **left** operand;
- if the left operand equals the identity-extension of `tgt^c` of the right
  (IC12), the composite is the **right** operand;
- otherwise the composition is not typeable in the free model.

This formulation is manifestly tied to the axioms that justify it, and I checked
it returns the correct answer on all three worked examples (both identity laws and
the paper's `u ∘₁ u`). So this is both a cleaner implementation and a correction
to the paper's lemma statement.
