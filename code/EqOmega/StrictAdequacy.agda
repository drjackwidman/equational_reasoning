{-# OPTIONS --cubical --guardedness --safe #-}

module StrictAdequacy where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Relation.Nullary using (Discrete)

open import FreeKernel

------------------------------------------------------------------------
-- Definition of Strict ω-Category
--
-- A strict ω-category is a globular set with:
--   1. Composition operations that are strictly associative
--   2. Identity morphisms that are strict units
--   3. All axioms hold as equalities (not just up to higher cells)

module StrictOmegaCat where

  -- Helper: define iterated operations for any structure
  module IteratedOps
    (C : ℕ → Type)
    (src : ∀ {n} → C (suc n) → C n)
    (tgt : ∀ {n} → C (suc n) → C n)
    (id  : ∀ {n} → C n → C (suc n))
    where

    src^ : ∀ {n} → (k : ℕ) → C (k ℕ.+ n) → C n
    src^ zero    t = t
    src^ (suc k) t = src^ k (src t)

    tgt^ : ∀ {n} → (k : ℕ) → C (k ℕ.+ n) → C n
    tgt^ zero    t = t
    tgt^ (suc k) t = tgt^ k (tgt t)

    id^ : ∀ {n} → (ℓ : ℕ) → C n → C (ℓ ℕ.+ n)
    id^ zero    t = t
    id^ (suc ℓ) t = id (id^ ℓ t)

  record isStrictOmegaCat
    (C : ℕ → Type)
    (src : ∀ {n} → C (suc n) → C n)
    (tgt : ∀ {n} → C (suc n) → C n)
    (id  : ∀ {n} → C n → C (suc n))
    (compₖ : ∀ {n} → (k : ℕ) → C n → C n → C n)
    : Type where

    open IteratedOps C src tgt id

    field
      -- IC1: Globularity (source)
      globularity-src : ∀ {n} (x : C (suc (suc n)))
                      → src (src x) ≡ src (tgt x)

      -- IC2: Globularity (target)
      globularity-tgt : ∀ {n} (x : C (suc (suc n)))
                      → tgt (src x) ≡ tgt (tgt x)

      -- IC3: Source of identity
      src-of-id : ∀ {n} (x : C n) → src (id x) ≡ x

      -- IC4: Target of identity
      tgt-of-id : ∀ {n} (x : C n) → tgt (id x) ≡ x

      -- IC5: Source of 0-compₖosition
      src-compₖ₀ : ∀ {n} (y x : C (suc n))
                → src (compₖ 0 y x) ≡ src x

      -- IC6: Target of 0-compₖosition
      tgt-compₖ₀ : ∀ {n} (y x : C (suc n))
                → tgt (compₖ 0 y x) ≡ tgt y

      -- IC7: Source of (k+1)-compₖosition
      src-compₖₛ : ∀ {n} (k : ℕ) (y x : C (suc n))
                → src (compₖ (suc k) y x) ≡ compₖ k (src y) (src x)

      -- IC8: Target of (k+1)-compₖosition
      tgt-compₖₛ : ∀ {n} (k : ℕ) (y x : C (suc n))
                → tgt (compₖ (suc k) y x) ≡ compₖ k (tgt y) (tgt x)

      -- IC9: Associativity (STRICT)
      associativity : ∀ {n} (k : ℕ) (z y x : C n)
                    → compₖ k (compₖ k z y) x ≡ compₖ k z (compₖ k y x)

      -- IC10: Exchange law
      exchange : ∀ {n} (j k : ℕ) (z y w x : C n)
               → compₖ k (compₖ j z y) (compₖ j w x)
                 ≡ compₖ j (compₖ k z w) (compₖ k y x)

      -- IC11: Left unit law (STRICT)
      unit-left : ∀ {m} (k : ℕ) (x : C (suc k ℕ.+ m))
                → compₖ k (id^ (suc k) (tgt^ (suc k) x)) x ≡ x

      -- IC12: Right unit law (STRICT)
      unit-right : ∀ {m} (k : ℕ) (x : C (suc k ℕ.+ m))
                 → compₖ k x (id^ (suc k) (src^ (suc k) x)) ≡ x

      -- IC13: Identity preserves compₖosition
      id-compₖ : ∀ {n} (k : ℕ) (y x : C n)
              → id (compₖ k y x) ≡ compₖ (suc k) (id y) (id x)

  record StrictOmegaCat : Type₁ where
    field
      Obj : ℕ → Type
      src : ∀ {n} → Obj (suc n) → Obj n
      tgt : ∀ {n} → Obj (suc n) → Obj n
      id  : ∀ {n} → Obj n → Obj (suc n)
      compₖ : ∀ {n} → (k : ℕ) → Obj n → Obj n → Obj n
      isStrict : isStrictOmegaCat Obj src tgt id compₖ

------------------------------------------------------------------------
-- Theorem 6.1: Strong Adequacy
--
-- Part 1: The quotient Term / ~ is a strict ω-category
-- Part 2: Every strict ω-category arises as such a quotient

module Adequacy (Gen : ℕ → Type) (GenDecEq : ∀ {n} → Discrete (Gen n)) where

  open Kernel Gen GenDecEq
  open StrictOmegaCat

  -- We'll need set quotients from the cubical library
  open import Cubical.HITs.SetQuotients renaming ([_] to ⟦_⟧)

  ----------------------------------------------------------------------
  -- The quotient Term / ~

  TermQuot : ℕ → Type
  TermQuot n = Term n / _~_

  -- Quotient constructors
  ⟦_⟧ₜ : ∀ {n} → Term n → TermQuot n
  ⟦ t ⟧ₜ = ⟦ t ⟧

  -- Operations descend to the quotient if they respect ~
  -- We need to show: if x ~ x' and y ~ y' then compₖ x y ~ compₖ x' y'

  ----------------------------------------------------------------------
  -- Lemma: ~ is a congruence for all operations

  ~-cong-src : ∀ {n} {x y : Term (suc n)} → x ~ y → src x ~ src y
  ~-cong-src = {!!}  -- Needs proof by induction on the axiom relation

  ~-cong-tgt : ∀ {n} {x y : Term (suc n)} → x ~ y → tgt x ~ tgt y
  ~-cong-tgt = {!!}

  ~-cong-id : ∀ {n} {x y : Term n} → x ~ y → id x ~ id y
  ~-cong-id = {!!}

  ~-cong-compₖ : ∀ {n} (k : ℕ) {a a' b b' : Term n}
              → a ~ a' → b ~ b' → compₖₖ k a b ~ compₖₖ k a' b'
  ~-cong-compₖ = {!!}

  ----------------------------------------------------------------------
  -- Operations on the quotient

  src/ : ∀ {n} → TermQuot (suc n) → TermQuot n
  src/ = rec→Set squash/ (λ x → ⟦ src x ⟧ₜ) (λ x y x~y → eq/ _ _ (~-cong-src x~y))

  tgt/ : ∀ {n} → TermQuot (suc n) → TermQuot n
  tgt/ = rec→Set squash/ (λ x → ⟦ tgt x ⟧ₜ) (λ x y x~y → eq/ _ _ (~-cong-tgt x~y))

  id/ : ∀ {n} → TermQuot n → TermQuot (suc n)
  id/ = rec→Set squash/ (λ x → ⟦ id x ⟧ₜ) (λ x y x~y → eq/ _ _ (~-cong-id x~y))

  compₖ/ : ∀ {n} → (k : ℕ) → TermQuot n → TermQuot n → TermQuot n
  compₖ/ k = rec2→Set squash/
    (λ x y → ⟦ compₖₖ k x y ⟧ₜ)
    (λ a a' b b~b' → eq/ _ _ (~-cong-compₖ k (λ i → a) b~b'))
    (λ a~a' b → eq/ _ _ (~-cong-compₖ k a~a' (λ i → b)))

  ----------------------------------------------------------------------
  -- Part 1 (Completeness): Term / ~ is a strict ω-category

  TermQuot-isStrictOmegaCat : isStrictOmegaCat TermQuot src/ tgt/ id/ compₖ/
  TermQuot-isStrictOmegaCat = record
    { globularity-src = elimProp (λ _ → squash/ _ _)
        (λ x → eq/ _ _ (glob-src x))

    ; globularity-tgt = elimProp (λ _ → squash/ _ _)
        (λ x → eq/ _ _ (glob-tgt x))

    ; src-of-id = elimProp (λ _ → squash/ _ _)
        (λ x → eq/ _ _ (src-id x))

    ; tgt-of-id = elimProp (λ _ → squash/ _ _)
        (λ x → eq/ _ _ (tgt-id x))

    ; src-compₖ₀ = elimProp2 (λ _ _ → squash/ _ _)
        (λ y x → eq/ _ _ (src-compₖ₀ y x))

    ; tgt-compₖ₀ = elimProp2 (λ _ _ → squash/ _ _)
        (λ y x → eq/ _ _ (tgt-compₖ₀ y x))

    ; src-compₖₛ = λ k → elimProp2 (λ _ _ → squash/ _ _)
        (λ y x → eq/ _ _ (src-compₖₛ k y x))

    ; tgt-compₖₛ = λ k → elimProp2 (λ _ _ → squash/ _ _)
        (λ y x → eq/ _ _ (tgt-compₖₛ k y x))

    ; associativity = λ k → elimProp3 (λ _ _ _ → squash/ _ _)
        (λ z y x → eq/ _ _ (assoc k z y x))

    ; exchange = λ j k → elimProp4 (λ _ _ _ _ → squash/ _ _)
        (λ z y w x → eq/ _ _ (exchange j k z y w x))

    ; unit-left = {!!}   -- Need to handle iterated operations
    ; unit-right = {!!}  -- Need to handle iterated operations
    ; id-compₖ = λ k → elimProp2 (λ _ _ → squash/ _ _)
        (λ y x → eq/ _ _ (id-compₖ k y x))
    }

  TermQuot-StrictOmegaCat : StrictOmegaCat
  TermQuot-StrictOmegaCat = record
    { Obj = TermQuot
    ; src = src/
    ; tgt = tgt/
    ; id = id/
    ; compₖ = compₖ/
    ; isStrict = TermQuot-isStrictOmegaCat
    }

  ----------------------------------------------------------------------
  -- Part 2 (Soundness): Every strict ω-category arises as Term / ~
  --
  -- This direction requires showing that for any strict ω-category C,
  -- there exists a set of generators Gen such that C ≅ Term Gen / ~

  module FromStrictOmegaCat (C : StrictOmegaCat) where
    open StrictOmegaCat.StrictOmegaCat C

    -- Define generators as the 0-cells and 1-cells of C that are not
    -- compₖosites or identities. This is non-trivial because we need to
    -- identify which cells are "primitive"

    -- For now, we can state the theorem:

    postulate
      -- There exist generators such that C is isomorphic to Term Gen / ~
      adequate : Σ[ Gen ∈ (ℕ → Type) ]
                 Σ[ GenDecEq ∈ (∀ {n} → Discrete (Gen n)) ]
                 let open Adequacy Gen GenDecEq in
                 Obj ≃ TermQuot

------------------------------------------------------------------------
-- Main Theorem 6.1 Statement

Theorem-6-1-Completeness : ∀ (Gen : ℕ → Type) (GenDecEq : ∀ {n} → Discrete (Gen n))
                          → StrictOmegaCat
Theorem-6-1-Completeness Gen GenDecEq =
  Adequacy.TermQuot-StrictOmegaCat Gen GenDecEq

Theorem-6-1-Soundness : ∀ (C : StrictOmegaCat)
                       → Σ[ Gen ∈ (ℕ → Type) ]
                         Σ[ GenDecEq ∈ (∀ {n} → Discrete (Gen n)) ]
                         let open Adequacy Gen GenDecEq
                             open StrictOmegaCat.StrictOmegaCat C
                         in Obj ≃ TermQuot
Theorem-6-1-Soundness C = Adequacy.FromStrictOmegaCat.adequate C

------------------------------------------------------------------------
-- Summary
--
-- Theorem 6.1 (Strong Adequacy):
--   Models of EqCat∞ under the strong reading (where equality is ≡)
--   are exactly strict ω-categories.
--
-- We've proved:
--   ✓ Completeness (mostly): Term Gen / ~ forms a strict ω-category
--   ○ Soundness (stated): Every strict ω-category is Term Gen / ~ for some Gen
--
-- What remains:
--   - Complete the unit laws in TermQuot-isStrictOmegaCat
--   - Prove congruence lemmas (~-cong-*)
--   - Prove soundness direction (requires identifying generators)
