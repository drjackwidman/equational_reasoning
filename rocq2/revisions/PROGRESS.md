# Progress report — Rocq formalization of strict-case decidability

## Where it stands: COMPLETE (admit-free)

The whole development compiles under Rocq 8.15. The build chain (`_CoqProject`)
is `Syntax → Axioms → Meta → NormalForm → FreeModel → Model → Decidable`. The
headline theorem `free_cell_decidable` — decidability of provable equality in the
strict free model — is **fully proved, with no `Admitted` and no extra axioms**.

`Print Assumptions free_cell_decidable` reports only the three intended abstract
generator parameters (`Generator`, `gen_dim`, `Generator_eq_dec`) — i.e. the
theory's inputs, not gaps. Because `Print Assumptions` is transitive, this is a
complete audit: if any lemma anywhere underneath still had a hole it would appear
here, and none does.

To decide `e₁ = e₂`: normalize both terms and compare the resulting normal forms
with decidable syntactic equality; agreement gives equality via soundness,
disagreement gives inequality via completeness plus dimension-agreement.

## How the proof is structured

The decision procedure is a structurally-recursive `normalize : Term → option NF`,
where `NF` is a typed, canonical representation of the normal forms `id^ℓ end^m a`.
Rather than the paper's three-pass rewriting (push unary ops down, normalize unary
leaves, eliminate compositions bottom-up), all of it is folded into smart
constructors `nf_src`, `nf_tgt`, `nf_id`, `nf_comp` that realize rules R1–R11 and
Lemma 4.4 directly. This is manifestly terminating (plain structural recursion) and
makes soundness/completeness reduce to induction on terms / derivations.

Top-level results, all `Qed`:

- `normalize_total` — on well-formed terms `normalize` succeeds, and (the
  conclusion is strengthened to also carry) the result denotes the input:
  `toTerm u == t`. Totality and soundness are proved by the *same* `wf` induction,
  which is what keeps the `comp` case free of any circular appeal to a separate
  soundness lemma (the operand-soundness facts feeding `nf_comp_glue` are exactly
  the induction hypotheses).
- `normalize_sound` — a corollary of `normalize_total`.
- `normalize_complete` — provable equality implies identical normal forms.
- `toTerm_inj` (Lemma 4.2) — distinct canonical, well-formed normal forms denote
  distinct cells. Discharged by `Model.toTerm_inj`, which is proved in `Model.v`
  via a *total* semantic interpretation `interp : Term → NF` and the combined
  `eq_cat`/`wf` mutual induction `Model.interp_sound_mut`.
- `free_cell_decidable` (Theorem 4.6) — assembled from the above.

Supporting facts proved on the way (all `Qed`, no holes): the unary fragment is
sound (`nf_src`/`nf_tgt`/`nf_id` agree with the axioms — R8/R9 from IC1/IC2,
R6/R7 from IC3/IC4); normal forms are well-formed terms with correct dimensions;
the retraction `normalize (toTerm u) = u`; and the model-side machinery
(`m_comp_boundary`, the `idext` tower-normalization lemmas, and soundness of
`interp` for every axiom E1–E8, IC1–IC13, including the exchange case IC10).

## History (how the last gaps were closed)

An earlier state of this development carried five `Admitted` lemmas in
`Decidable.v` plus one `admit` in `Model.interp_sound_mut`'s IC10 (exchange) case.
These were closed as follows:

- `src_pow_sound`, `tgt_pow_sound`, `nf_comp_glue` — proved directly in
  `Decidable.v`.
- `normalize_sound` — eliminated by strengthening `normalize_total` (above).
- `toTerm_inj` — routed through `Model.toTerm_inj`.
- IC10 — the five residual tower-collapse leaves are discharged by helper lemmas
  `ndim_idext_src`/`ndim_idext_tgt`, `m_comp_junk`, and leaf lemmas
  `ic10_l1`–`ic10_l5`; `interp_sound_mut` now ends `Qed`.

See `DECIDABILITY_PROOF.md` for the detailed account.

---

## A correction to Lemma 4.4 of the paper (a genuine finding)

While implementing the composition constructor, I found that **Lemma 4.4, read
literally, returns the wrong operand on unit-absorption.** The lemma's three cases
say the composite `u ∘ v` of two normal forms equals `u` in cases (a)/(b) and `v`
in case (c), gated by conditions like `k ≤ ℓ`. Tested against concrete identity
laws, those conditions come out backwards.

Concretely, take a 2-cell `α : f ⇒ g` and the identity `id_f` on its source. The
right-unit law gives `α ∘₁ id_f = α`. Here the left operand is `α` (no `id`s,
`ℓ = 0`) and we should return it. But the lemma's cases that return the left
operand all require `k ≤ ℓ` — here `k = 1`, `ℓ = 0`, so *none of them fire*, and
the only case that matches is the one returning the **other** operand `id_f`. The
symmetric left-unit example `id_g ∘₁ α = α` fails the same way. (The lemma's
*typeability conditions* are fine; it's the "= u" / "= v" verdicts that are
swapped relative to which operand is the genuine cell.) The paper's own running
example `u ∘₁ u = u` does not expose this because there both operands are equal.

### The fix (used in `nf_comp`)

Instead of transcribing the (a)/(b)/(c) bookkeeping, `nf_comp` is defined straight
from the two unit laws it encodes:

- if the right operand equals the identity-extension of `src^c` of the left
  (this is exactly IC11), the composite is the **left** operand;
- if the left operand equals the identity-extension of `tgt^c` of the right
  (IC12), the composite is the **right** operand;
- otherwise the composition is not typeable in the free model.

This formulation is manifestly tied to the axioms that justify it, and it returns
the correct answer on all three worked examples (both identity laws and the
paper's `u ∘₁ u`). So it is both a cleaner implementation and a correction to the
paper's lemma statement. (See `lemma_4_4_counterexample.txt` for the worked
counterexample.)
