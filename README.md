# Equational Reasoning in ∞-Categories (Agda Formalization)

This repository contains a mechanization and experimental implementation of the equational calculus for ∞-categories described in the accompanying paper:

> **Equational Reasoning in ∞-Categories**

The goal of the project is to provide a constructive, machine-checkable framework for symbolic equational reasoning in higher categories, together with a normalization-based decision procedure for equality in the free model.

---

## Overview

This project develops a typed equational calculus for ∞-categories, together with a free model and normalization algorithm, and provides an Agda implementation of core components of this theory.

The central idea is to treat an ∞-category as a model of a typed equational theory of higher-dimensional cells equipped with:

- source and target maps  
- identities  
- higher-dimensional composition  
- equational reasoning principles  

The theory admits two interpretations:

- **Strong mode:** equations are literal identities (yielding strict ω-categories).
- **Weak mode:** equations are interpreted as equivalences (homotopies relative to boundary).

The Agda code in this repository focuses primarily on the syntactic and algebraic side: free constructions, normalization, and decision procedures for equality of well-formed terms.

---

## Main Contributions (Formalized)

The repository formalizes key ideas from the paper:

- A compact typed equational calculus for higher composition and identities.
- Construction of free ∞-categorical models from stratified sets of generators.
- A deterministic normalization procedure for well-typed terms.
- A decision procedure for equality of closed terms in the free model.
- Infrastructure for mechanized equational reasoning in higher categories.

In the free model, equality is decided by computing normal forms and comparing them syntactically.

---

## Repository Structure


---

## `FreeKernel.agda`

This file contains the core implementation of:

- the syntax of higher-dimensional terms
- typing / well-formedness constraints
- normalization rules
- the kernel of the decision procedure for equality in the free ∞-category

It encodes the rewriting system corresponding to the equational Horn theory described in the paper, including rules governing:

- source/target behavior under composition
- identities
- globularity
- exchange laws

---

## The Equational Calculus

The calculus treats higher cells as typed expressions with dimension annotations. The basic operations include:

- `src`, `tgt` : source and target maps  
- `id` : identity cells  
- `◦ₖ` : k-dimensional composition  
- equality as derivability in an equational Horn logic  

The equational theory includes:

- reflexivity, symmetry, transitivity, and congruence
- globularity axioms
- interaction laws between identities and composition

These rules provide a symbolic calculus that can be interpreted either strictly (as equalities) or weakly (as equivalences / homotopies).

---

## Free Model and Normalization

Given a stratified set of generators (cells with assigned dimensions), the free ∞-category is constructed as well-formed terms modulo provable equations.

A key feature formalized here is:

> A deterministic normalization algorithm that computes normal forms of terms;  
> two terms are equal in the free model **iff** their normal forms coincide.

Normal forms have a canonical shape built from iterated identities and boundary operators applied to primitive generators.

This yields:

- decidable equality of ground terms
- rewriting-based automation
- a constructive basis for mechanized higher-categorical reasoning

---

## Strong vs. Weak Interpretations

The same equational syntax supports two semantic readings:

- **Strong reading:** equations are strict identities, yielding strict ω-categories.
- **Weak reading:** equations are interpreted as equivalences witnessed by higher cells (e.g., homotopies relative to boundary).

This duality allows one to derive symbolic equations in the strict mode and interpret them homotopically in the weak mode without changing the syntax.

---




## Research Context

This repository is intended for:

- researchers in higher category theory
- homotopy type theory and ∞-categories
- formalization of algebraic and higher-categorical structures
- constructive and mechanized reasoning about higher-dimensional algebra

It provides an experimental bridge between:

- symbolic equational reasoning, and
- homotopical semantics of higher categories

---

## Future Directions

Possible extensions include:

- mechanizing the weak (homotopical) interpretation
- integrating with cubical type theory
- automation tactics for rewriting in higher categories
- connections to strictification and coherence theorems
- decision procedures beyond the free model (where undecidability appears)

---

## Reference

This work accompanies the preprint:

> **Equational Reasoning in ∞-Categories**  
> Anonymous authors

---

## Author of Agda Code

**Jack Widman**  
PhD in Mathematics — Topology, Type Theory, and Higher Categories  
Research Fellow, Ben-Gurion University, Department of Computer Science
