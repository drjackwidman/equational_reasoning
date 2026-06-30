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

`Print Assumptions` lists the remaining holes. The three `Syntax.Generator*` /
`Syntax.gen_dim` lines are the theory's intended abstract `Parameter`s, **not**
gaps. Anything else is a real `Admitted`.

## Build chain (`_CoqProject`)

`Syntax → Axioms → Meta → NormalForm → FreeModel → Model → Decidable`

`Model.v` was **added** to the chain (between `FreeModel` and `Decidable`) so that
`Decidable.v` can reuse its NF-level lemmas (`m_comp_boundary`, `NF_eqb_refl`,
`NF_eqb_eq`, `idext_*_canonical`, …). `Normalizer.v` remains obsolete and is not in
the build.

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

`Print Assumptions free_cell_decidable` currently reports exactly
`toTerm_inj` and `normalize_sound` (plus the `Generator*` parameters).

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

## The two remaining holes

### 1. `toTerm_inj` (Lemma 4.2) — reduces to one IC10 case

`toTerm_inj` is **already proved** in `Model.v` as `Model.toTerm_inj`. So
`Decidable.toTerm_inj` can become `Proof. exact Model.toTerm_inj. Qed.` once the
dependency below is closed.

`Model.toTerm_inj` → `Model.interp_sound` → **`Model.interp_sound_mut`**
(`Model.v`, `Admitted`), which is complete **except one `all: admit`** in the
**IC10 (exchange) case** (`Model.v:887`). The tower-normalization tactic there
closes 59 of 64 leaves; the rest are the hard combinatorial residue.

#### IC10 endgame — work in progress (NOT yet landed)

A standalone reproduction of the IC10 case (`IC10_case`) is being developed in
the scratch dir. Current scratch:
`/tmp/claude-1000/-home-jackwidman-agda-projects-equational-reasoning-rocq2-revisions/414d89e8-c03d-4a0b-a84a-d966532b4366/scratchpad/ic10i.v`
(iterations `ic10b..ic10i.v`).

Findings / approach that works:
- After the existing `gres` + `reflexivity`, each surviving leaf is a system of 6
  identity-extension equations (e.g. `interp x = idext_tgt (d-n) (interp w)`, …)
  whose conclusion is either an operand equality `interp p = interp q` or a
  residual `m_comp` term.
- The **original `rewrite H in *; clear H` block was destructive** — it discarded
  the boundary equations that several leaves need, which is why those 5 looked
  unprovable. The fix is to **not** clear, and resolve cleanly:
  1. Resolve residual `m_comp`s while operands are still clean `interp` vars:
     `m_comp k u u` via **`m_comp_diag`**; otherwise via a new lemma
     **`m_comp_val`** : `canonical u → canonical v →
     m_comp k u v = u ∨ (m_comp k u v = v ∧ u = idext_tgt (ndim u - k) v)`.
  2. Normalize `ndim (interp _)` to `d` (single optional pass —
     `rewrite ?HnX,?HnY,?HnZ,?HnW in *`; **note** a `repeat … in *` here
     self-loops because it rewrites `HnX : ndim (interp x) = d` into `d = d`).
  3. Each leaf then reduces to `interp p = interp q`, provable by oriented
     rewriting with the hypotheses + **equal-codim cancellation**
     (`idext_tgt c (idext_src c ·) = idext_src c ·`, etc.). Crucially the rewrite
     **order matters** (the variable system is cyclic; only one order triggers the
     cancellation), so the leaf solver must **backtrack** — a recursive
     `multimatch` tactic `sleaf` with fuel.
- New helper lemmas needed (proved in scratch, to be moved into `Model.v`):
  - `idext_tgt_idext_src : idext_tgt c (idext_src c v) = idext_src c v`
    (mirror of the existing `idext_src_idext_tgt`).
  - `m_comp_val` (above).
- **Pending next step:** the last scratch run failed only because `sleaf`'s
  self-reference *guard* (`assert_fails (lazymatch …)`) mis-fires; with diagonal
  `m_comp`s handled by `m_comp_diag` there are no self-referential hypotheses, so
  the guard should simply be **dropped** and `sleaf` rerun. That edit was about to
  be tested when work paused. Expected outcome: full `Qed` of `IC10_case`, then
  port the tactic block into `Model.interp_sound_mut`'s IC10 case (replacing
  `all: admit`).

Sketch of the closer to land in `Model.v` (after the existing `gres; try reflexivity`):
```coq
all: try (repeat match goal with
            | [ |- context[m_comp ?k ?u ?u] ] => rewrite (m_comp_diag k u)
            | [ |- context[m_comp ?k ?u ?v] ] =>
                destruct (m_comp_val k u v ltac:(can) ltac:(can)) as [Hmv|[Hmv Hmq]];
                rewrite Hmv; clear Hmv
          end).
all: rewrite ?HnX, ?HnY, ?HnZ, ?HnW in *.   (* single pass, not repeat *)
all: try clear HnX HnY HnZ HnW.
all: sleaf 8.
```
with
```coq
Ltac can := solve [ repeat (first [apply idext_src_canonical | apply idext_tgt_canonical]); apply interp_canonical ].
Ltac twr := repeat (first [ rewrite idext_src_idem | rewrite idext_tgt_idem
                          | rewrite idext_src_idext_tgt | rewrite idext_tgt_idext_src ]).
Ltac sleaf n := twr;
  first [ reflexivity
        | lazymatch n with
          | S ?n' => multimatch goal with
                     | [ H : interp ?v = _ |- context[interp ?v] ] => rewrite H; sleaf n'
                     end
          end ].
```
(Note: the IC10 case currently keeps `HnX..HnW` via `pose proof (interp_ndim …)`.)

### 2. `normalize_sound` — the deep one, untouched

`normalize_sound : wf t d → normalize t = Some u → toTerm u == t`. To be proved by
mutual induction over the combined `wf`/`eq_cat` judgment; hard cases IC9/IC10.
Its dependencies (`toTerm_inj`, `nf_comp_glue`, `*_pow_sound`) are now all in
place. **Strategic note:** `Model.interp_sound_mut` already *is* a soundness proof
of the total interpretation `interp` by the very mutual induction this needs, with
IC9/IC10 already worked out — so it may be far cheaper to prove `normalize_sound`
by routing through `interp` (e.g. `normalize t = Some u → interp t = u`, plus
`interp`/`toTerm` inversion) than to redo the IC9/IC10 induction from scratch.
Decide this before diving in.

## Housekeeping

A stale duplicate build tree `./tmp/equational_reasoning/decidability/` (an old
snapshot whose `.vo` files collided on the recursive `-R .` path and broke the
build) was moved to the scratch dir
(`…/scratchpad/tmp_stale_snapshot`). Restore or delete as desired.
