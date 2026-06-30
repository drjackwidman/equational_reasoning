# Decidability proof — current state

Goal: an admit-free proof of `free_cell_decidable` (Theorem 4.6), decidability of
provable equality in the strict free model of EqCat∞.

## STATUS: COMPLETE (admit-free)

`free_cell_decidable` is now proved with **no** `Admitted` and **no** extra
axioms. `Print Assumptions free_cell_decidable` lists exactly the three intended
abstract parameters (`Syntax.Generator`, `Syntax.gen_dim`,
`Syntax.Generator_eq_dec`) and nothing else. All seven files of the build chain
compile clean. The historical notes below are retained as a record of how the
last gaps were closed.

What closed the three former gaps:
- **`normalize_sound`** — strengthened `normalize_total` to carry the soundness
  conjunct `toTerm u == t` by the same `wf` induction (the `comp` case sources
  operand soundness from the IH, not from a free-standing lemma), then
  `normalize_sound` is a `Qed` corollary.
- **`toTerm_inj`** — `Decidable.toTerm_inj := Model.toTerm_inj` (`exact`).
- **`Model.interp_sound_mut` IC10 case** — the `all: admit` (5 residual leaves)
  is discharged by helper lemmas `ndim_idext_src`/`ndim_idext_tgt`,
  `m_comp_junk`, and five leaf lemmas `ic10_l1`–`ic10_l5`; `interp_sound_mut`
  now ends `Qed`. See the IC10 closer in `Model.v`.

## How to check status

```sh
cd <this dir>
# build chain
for f in Syntax Axioms Meta NormalForm FreeModel Model Decidable; do coqc -R . EqCat $f.v; done
# audit the only thing that matters — what the top theorem still rests on:
echo 'Require Import EqCat.Decidable. Print Assumptions free_cell_decidable.' | coqtop -R . EqCat 2>/dev/null
```

`Print Assumptions` should now list **only** the three `Syntax.Generator*` /
`Syntax.gen_dim` lines — the theory's intended abstract `Parameter`s, **not**
gaps. Anything else (an `Admitted`, or an extra `Axiom`) would be a regression.

## Build chain (`_CoqProject`)

`Syntax → Axioms → Meta → NormalForm → FreeModel → Model → Decidable`

`Model.v` was **added** to the chain (between `FreeModel` and `Decidable`) so that
`Decidable.v` can reuse its NF-level lemmas (`m_comp_boundary`, `NF_eqb_refl`,
`NF_eqb_eq`, `idext_*_canonical`, …).

## Score

Started at **5** admitted lemmas in `Decidable.v`. Now **0** remain (and the one
remaining `Model.v` admit, the IC10 case, is also closed).

| Lemma | File | Status |
|-------|------|--------|
| `src_pow_sound` | Decidable.v | ✅ proved |
| `tgt_pow_sound` | Decidable.v | ✅ proved |
| `nf_comp_glue`  | Decidable.v | ✅ proved |
| `toTerm_inj`    | Decidable.v | ✅ proved (= `Model.toTerm_inj`) |
| `normalize_sound` | Decidable.v | ✅ proved (corollary of `normalize_total`) |
| `interp_sound_mut` (IC10) | Model.v | ✅ proved (`ic10_l1`–`ic10_l5`) |

`Print Assumptions free_cell_decidable` now reports only the three `Generator*` /
`gen_dim` parameters — every lemma in the table above is `Qed`.

### What was done for the three closed lemmas

- **`src_pow_sound` / `tgt_pow_sound`**
  `toTerm (src_pow c u) == iter_src c (toTerm u)` (and tgt mirror). Proved by a
  case split mirroring `src_pow`'s definition, on two new helpers:
  - `iter_src_id_cancel` : `iter_src c (iter_id c Y) == Y` — `c` sources cancel
    `c` identities pairwise via **IC3** (resp. **IC4** for tgt). No dim bound.
  - `iter_src_end_build` : extra sources pile onto an end-block into a single
    `Es`-block, iterating the existing `src_end_collapse` (IC1/IC2).
  Plus utility `iter_inside` (inside-peel for `Nat.iter`, missing from stdlib) and
  `iter_id_cong`. These live in `Decidable.v` just after `iter_src_cong` /
  `iter_tgt_cong` (which they depend on); the old admit site is a pointer comment.

- **`nf_comp_glue`** (Lemma 4.4 combinatorial step).
  **Signature was augmented** with two extra hypotheses `toTerm u == a` and
  `toTerm v == b`. Rationale: the conclusion mentions the original `comp k a b`,
  and the only bridge from `u,v` to `a,b` is soundness of `normalize` — i.e.
  `normalize_sound`, whose own `comp` case *calls* `nf_comp_glue`. Passing the
  soundness facts in (they are exactly the IHs available at the sole call site,
  `normalize_total`, as `Hsu`/`Hsv`) keeps `nf_comp_glue` **independent of**
  `normalize_sound`, avoiding a circular dependency. The call site was updated to
  pass `Hsu Hsv`.
  Proof: derive the term-level boundary `iter_src c a == iter_tgt c b` from the NF
  boundary (using the now-proved `*_pow_sound`), so `comp k a b` is well-formed;
  then `m_comp_boundary` (from `Model.v`) splits the matched boundary into the two
  unit patterns; `nf_comp` returns the surviving operand and **E7_comp + IC11/IC12**
  identify it with `comp k a b`. The "no match" branch is a contradiction.
  Verified that `Model.v`'s IC10 admit did **not** leak in (the reused lemmas are
  all `Qed` and independent of `interp_sound_mut`).

## How the final two gaps were closed

### `toTerm_inj` (Lemma 4.2)

`Decidable.toTerm_inj` is `Proof. exact Model.toTerm_inj. Qed.` `Model.toTerm_inj`
is proved in `Model.v` from the total semantic interpretation `interp : Term → NF`
via `Model.interp_sound` / **`Model.interp_sound_mut`** (the combined `eq_cat`/`wf`
mutual induction), which now ends `Qed`.

The last obstacle was a single `all: admit` in `interp_sound_mut`'s **IC10
(exchange)** case: after the tower-normalization block closes 59 of 64 leaves, five
residual leaves remain. They are NF-equalities between iterated identity-extension
towers over an arbitrary canonical base `B` (`= interp x/y/z`, `ndim B = d`), with
`cm := d-m`, `cn := d-n`. They are discharged by these additions to `Model.v`:

- `ndim_idext_src` / `ndim_idext_tgt` — `ndim (idext_* c u) = ndim u` when
  `c ≤ ndim u` (the budget condition forces the no-truncation branch). These supply
  the `ndim u = d` side-conditions of `m_comp_idsrc` / `m_comp_idtgt` for tower
  operands.
- `m_comp_junk` — the else-branch of `m_comp` returns its left operand, given that
  the only way the left could be a target-unit of the right is if the two coincide.
- leaf lemmas `ic10_l1`–`ic10_l5`, one per residual shape, each resolving its
  `m_comp` via `m_comp_idsrc` / `m_comp_idtgt` plus a tower lemma
  (`ov_ss` / `ov_ts` / definitional). They use the **boundary equations** to pick
  the true unit pattern — *not* a blind `m_comp` value disjunction, which would
  spawn unprovable spurious branches.

The IC10 closer is then
`all: first [eapply ic10_l1 | … | eapply ic10_l5]`, followed by discharging the
`canonical` / `ndim = d` / codim side-goals (re-run after `Unshelve`, since
`eapply` shelves the `ndim` obligations). The `ndim` goals are closed by
`apply interp_ndim; assumption` — the residual context has no bare
`ndim (interp x) = d` hypothesis (it was consumed by the earlier rewrites).

### `normalize_sound`

Eliminated rather than proved separately. `normalize_total`'s conclusion was
strengthened to also carry the soundness conjunct `toTerm u == t`, proved by the
*same* `wf` induction; the `comp` case takes the operand-soundness facts
`Hsu`/`Hsv` from its induction hypotheses (not from a free-standing lemma), which
removes the old circularity. `normalize_sound` is then a one-line corollary of
`normalize_total`.
