# What backs the blurb

The blurb:

> a compact typed equational calculus for higher dimensional composition whose
> purpose is to isolate a small but pervasive proof engineering fragment of
> higher categorical reasoning. In practice, this fragment consists of boundary
> matching, repeated source and target simplification, identity propagation,
> and equality of closed terms in the free setting. These obligations arise
> constantly in higher categorical calculations, both formal and informal, and
> are often technically tedious even when conceptually routine. Our
> contribution is to package this layer as a simple equational system with
> strict adequacy and a normalization based decision procedure in the free
> setting, so that these recurring obligations reduce to comparison of normal
> forms.

This directory (`rocq3/`) is the mechanized artifact for that claim. Below,
each phrase of the blurb is matched to a named theorem, definition, or tactic.
Everything compiles under Coq 8.15 with no `Admitted` and no axioms beyond the
three generator parameters, which disappear on instantiation
(`Print Assumptions` in `Examples.v` reports "Closed under the global context").

## Phrase by phrase

| Blurb | Artifact |
|---|---|
| "compact typed equational calculus" | `Syntax.v` (terms, `dim`), `Axioms.v` (`wf` and `eq_cat`, mutually inductive; D1–D4, E1–E8, IC1–IC13) |
| "boundary matching" | the boundary premise of `wf_comp`; decided by `wfb` (`Reflect.v`), tactic `eqcat_wf` |
| "repeated source and target simplification" | rules R1–R9 as `nf_src`, `nf_tgt`, `src_pow`, `tgt_pow` (`NormalForm.v`); examples `st_*` |
| "identity propagation" | IC11–IC13 as `idext_src`, `idext_tgt`, `nf_id`, unit branches of `nf_comp`; examples `id_*` |
| "equality of closed terms in the free setting" | `free_cell_decidable` (Theorem 4.6, `Decidable.v`), now transparent and executable; `check_eq`, tactic `eqcat_decide` |
| "strict adequacy" | partially. `FreeModel_is_EqCat_model` (`Adequacy.v`) shows the free model satisfies every law of Figure 2 as a structure (`IsEqCatModel`). The comparison with the classical definition of strict ω-category, which is what Theorem 6.1 states, is not mechanized. See below. |
| "normalization based decision procedure" | `normalize` with `normalize_total`, `normalize_sound`, `normalize_complete`, `toTerm_inj` |
| "reduce to comparison of normal forms" | `check_eq_sound` / `check_eq_complete`: `t1 == t2` iff both normalize and the normal forms coincide; the tactics discharge goals by `vm_compute; reflexivity` |
| "free setting" (scope limit) | `wfb` and `check_eq` work on closed terms over a concrete `GEN`; Section 5 of the paper shows the general problem with variables is undecidable, and nothing here claims otherwise |

## What is new in rocq3 relative to rocq2/revisions

1. **The chain is a functor over the generators.** `Syntax.v` declares a
   `Module Type GEN`; each file is a stage `XF (G : GEN)` that `Include`s the
   previous one. Users instantiate the top stage once with concrete generators
   (`Module E := AdequacyF Gen`). Consequence: `vm_compute` can run the
   normalizer, and `Print Assumptions` is closed. This touched every file but
   changed no proof.
2. **`free_cell_decidable` is `Defined`, not `Qed`.** The sumbool is now a
   program; `Examples.v` evaluates it.
3. **`Reflect.v`** (new). Boolean checkers `wfb`, `check_eq`, `check_neq` with
   soundness theorems, `check_eq_complete`, and tactics `eqcat_wf`,
   `eqcat_decide`, `eqcat_refute`, `mkcell`.
4. **`Adequacy.v`** (new). `OmegaSig` (cells, setoid equality, dimension,
   src/tgt/id, partial composition indexed by composability data) and
   `IsEqCatModel` (the laws of Figure 2 over such a signature: congruence,
   dimensions, globularity, identities, boundary of composites, associativity,
   exchange, unit laws, id/comp compatibility). `FreeModel_is_EqCat_model`
   proves the free model satisfies them. Each law is a single `eq_cat`
   constructor whose `wf` premises are the `cell_proof` components of the
   cells in the statement. This is the well-definedness of the quotient,
   stated as a structure. It is not Theorem 6.1; see the next section.
5. **`Examples.v`** (new). Thirty-one goals grouped by the four obligation
   kinds; twenty-nine closed by one tactic call, two ill-formedness checks
   closed by computation. Includes Example 4.3 from the paper,
   an associativity instance, an exchange instance across ∘₀/∘₁, negative
   examples closed by `eqcat_refute`, and the Lemma 4.4 counterexample.
6. `Free_id` and `Free_comp` in `FreeModel.v` are written with projections
   instead of `destruct`, so `cell_term (Free_comp ...)` reduces. Same cells.

## What the tactic does, concretely

Goal: `comp 1 (id (tgt alpha)) alpha == alpha` (left unit law on a 2-cell).

```
Proof. eqcat_decide. Qed.
```

`eqcat_decide` applies `check_eq_sound`, leaving `check_eq t1 t2 = true`.
`vm_compute` runs `wfb` on both sides (each boundary of each composite is
normalized and compared), runs `normalize` on both sides, compares the two
normal forms with `NF_eq_dec`, and reduces the whole thing to `true = true`.
`reflexivity` closes it. If the normal forms differ, or either side is
ill-formed, the goal reduces to `false = true` and the tactic fails, which is
the correct outcome.

## What is not mechanized

> **Update, 12 Nov 2026.** Theorem 6.1 is now mechanized in `Strict.v`
> (`adequacy`: `IsEqCatModel` is equivalent to `IsStrictOmegaCat`, both
> directions). The exchange rule `IC10` and the `exchange` law of
> `IsEqCatModel` now carry the paper's side condition m ≠ n; the theorem is
> false without it. `Universal.v` adds interpretation in a model, soundness,
> and the universal property of the free model. The first bullet below
> describes the state before this update.

- **Theorem 6.1 itself.** The record `IsEqCatModel` is Figure 2 transcribed.
  Theorem 6.1 says a model of Figure 2 is the same thing as a strict
  ω-category in the classical sense (each `C_k ⇉ C_ℓ` a category with
  composition along ℓ-cells, each `C_k ⇉ C_ℓ ⇉ C_m` a strict 2-category), and
  Appendix B sketches the translation in both directions. Neither direction is
  mechanized. To do it one needs a Rocq definition of classical strict
  ω-category (globular set plus the family of categories and 2-categories),
  a construction of an `OmegaSig` model from one and back, and proofs that the
  laws transfer. Appendix B also has an unfinished sentence in the reverse
  direction ("finish this one"). Since "strict adequacy" is a headline word in
  the blurb, this is the real remaining formalization work.
- **Models in general.** There is no Rocq notion of "model of EqCat∞ in an
  arbitrary category"; only the free model is treated. The syntactic-category
  notes in `rocq2/revisions/syntactic_category.md` are the starting point if
  that is wanted.
- **The weak reading** (Sections 7 and 8). Untouched; the blurb does not
  mention it.
- **Undecidability** (Section 5). Not formalized.

## One required change to the paper

Lemma 4.4, cases (b) and (c), return the wrong operand on unit absorption.
The worked counterexample is `lemma_4_4_counterexample.txt`, and `Examples.v`
contains it as two machine-checked facts:

```
Example lemma44_correct_value : comp 1 (id (tgt alpha)) alpha == alpha.
Example lemma44_wrong_value   : ~ (comp 1 (id (tgt alpha)) alpha == id (tgt alpha)).
```

The paper's case (b) asserts the second is an equality. The mechanized
`nf_comp` decides by boundary instead: if the right operand is the identity
extension of `src^c` of the left, return the left (IC11); if the left operand
is the identity extension of `tgt^c` of the right, return the right (IC12);
otherwise not typeable. The paper text of Lemma 4.4 and its proof in Appendix A
should be replaced by that rule. Under the new framing this matters: the
blurb's claim is that the algorithm is right.

## Build

```
cd rocq3
make          # ~25 s
make audit    # greps for Admitted/admit: none
```

Or by hand, in order: Syntax Axioms Meta NormalForm Model FreeModel Decidable
Reflect Adequacy Examples, each with `coqc -q -R . EqCat <file>.v`.
