# EqCat∞ — Decidability in the Strict Free Model

A Rocq (Coq) formalization of the decision procedure of §4 of *Equational
Reasoning in ∞-Categories*: deciding provable equality of closed terms in the
**strict free model** of the typed equational theory EqCat∞.

The headline target is

```coq
Theorem free_cell_decidable : forall c1 c2 : FreeCell, {c1 === c2} + {~ c1 === c2}.
```

(`Decidable.v`), i.e. equality in the free model is decidable: to decide
`e₁ = e₂`, normalize both terms and compare normal forms; agreement gives
equality by soundness, disagreement gives inequality by completeness plus
dimension agreement.

**Status caveat.** This theorem type-checks, but its proof currently rests on
five `Admitted` lemmas (see [Proof status](#proof-status)). The development
therefore establishes decidability **conditionally on those lemmas**, not yet
outright; `free_cell_decidable` is not a complete proof as it stands.

## Requirements

- **Coq 8.15** (developed and checked against 8.15.0).
- Standard library only — no external dependencies.

## Build

```sh
coq_makefile -f _CoqProject -o Makefile   # regenerate the build file
make                                        # compiles all six files
```

To audit exactly what the main theorem rests on:

```sh
coqc -R . EqCat <(echo 'Require Import Decidable. Print Assumptions free_cell_decidable.')
```

## File overview

The logical dependency order (also the order in `_CoqProject`):

| File           | Contents |
|----------------|----------|
| `Syntax.v`     | Raw terms, the partial `dim` function (D1–D4), iterated `src`/`tgt`/`id`, decidable equality on terms. |
| `Axioms.v`     | The mutually-inductive `wf` (well-formedness) and `eq_cat` (provable equality `==`) relations: structural axioms E1–E8 and ∞-categorical axioms IC1–IC13 (Figure 2). `wf_comp` carries the boundary condition `src^{n-k} a == tgt^{n-k} b`, which forces the mutual definition. |
| `Meta.v`       | Metatheory: `wf` determines dimension, and provable equality preserves dimension (`eq_cat_dim`, `eq_cat_dim_agree`). |
| `NormalForm.v` | Typed normal forms `id^ℓ end^m a` (Def 4.1), the structurally-recursive `normalize : Term → option NF`, and soundness of the unary smart constructors + a round-trip retraction `normalize (toTerm u) = u`. |
| `FreeModel.v`  | The free model as `FreeCell` (a term bundled with its `wf` proof), the setoid `===`, and the lifted operations `src`/`tgt`/`id`/`comp`. |
| `Decidable.v`  | Normalizer soundness/completeness/totality and `free_cell_decidable` (Theorem 4.6). |

The theory is parameterized over a set of generators (`Syntax.Generator`, `gen_dim`,
`Generator_eq_dec`); these are abstract `Parameter`s, as in the paper.

## Proof status

The development **compiles** under Coq 8.15, but it is **not yet a complete
proof**: five lemmas are `Admitted`, and the headline theorem depends on all of
them. An `Admitted` lemma is accepted by Coq on faith, so `make` succeeding does
**not** mean every result is established. To see exactly what the main theorem
rests on, run `Print Assumptions free_cell_decidable` — it reports the five
lemmas below.

### Genuinely unproven — 5 `Admitted` lemmas, all in `Decidable.v`

These isolate the deep combinatorial / confluence content of §4 and are the
remaining work:

- `toTerm_inj` — Lemma 4.2: distinct canonical, well-formed normal forms denote
  distinct cells (injectivity of the normal-form interpretation; the confluence core).
- `nf_comp_glue` — the Lemma 4.4 combinatorial step: a matched boundary makes the
  composite degenerate and `nf_comp` succeed.
- `normalize_sound` — `normalize` is sound with respect to `==`.
- `src_pow_sound`, `tgt_pow_sound` — the normal-form-level iterated `src`/`tgt`
  operators agree with the term-level ones.

### Proved outright — `Qed`, no admitted assumptions

- All of `Syntax`, `Axioms`, `Meta`, and `FreeModel`.
- In `NormalForm`: the normal-form representation, the `normalize` function,
  soundness of the unary smart constructors (`nf_src`/`nf_tgt`/`nf_id`), and the
  round-trip retraction `normalize (toTerm u) = u`.
- In `Decidable`: roughly twenty infrastructure lemmas (iterated `src`/`tgt`
  arithmetic and congruence, well-formedness / canonicity preservation, etc.).

### Proved only *conditionally* — `Qed`, but transitively assume the 5 lemmas above

`normalize_total`, `normalize_complete`, and `free_cell_decidable` carry `Qed`
proofs, but each is built **from** the five admitted lemmas and therefore inherits
those assumptions. The *architecture* of the decidability argument is complete and
the remaining gaps are clearly delimited — but decidability itself is established
only **modulo** `toTerm_inj`, `nf_comp_glue`, `normalize_sound`, `src_pow_sound`,
and `tgt_pow_sound`.

> Implementation note: rather than transcribing the paper's three-pass rewriting,
> `normalize` is a single structural recursion through smart constructors
> (`nf_src`, `nf_tgt`, `nf_id`, `nf_comp`). `nf_comp` is defined directly from the
> unit laws IC11/IC12. This was both cleaner to mechanize and surfaced a sign/operand
> issue in the literal statement of Lemma 4.4's unit-absorption cases; see the
> commit history / project notes for details.
