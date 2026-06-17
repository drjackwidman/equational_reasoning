(** * Syntax of EqCat∞
    Raw terms, dimension, well-formedness, and decidable equality.
    Reference: "Equational Reasoning in ∞-Categories" §3.1.1, Figure 2 (D1–D4). *)

(* JW: Revision notes (in response to Liron's review).
   Two changes in this file, both prompted by her comments:
     1. The inductive [wf] judgment that mirrors D1–D4 of Figure 2 has
        been MOVED out of this file. It now lives in [Axioms.v] because
        the [wf_comp] case requires the boundary condition
            src^{n-k} a == tgt^{n-k} b
        which is expressed in the theory's own equality [eq_cat], so
        [wf] and [eq_cat] must be defined mutually. The boundary-free
        partial function [dim] stays here unchanged.
     2. Added named aliases [iter_src], [iter_tgt], [iter_id] for
        [Nat.iter k {src,tgt,id}]. Used in the boundary premise of
        [wf_comp] and in IC11–IC13. Pure abbreviations.
   Old [Definition wf := exists n, dim t = Some n] is gone; the new
   inductive [wf] is in [Axioms.v]. *)

Require Import Arith.
Require Import PeanoNat.
Require Import Bool.

(** ** Generators
    The theory is parameterized by a set of generators, each with a fixed
    dimension, and decidable equality. *)
Parameter Generator    : Type.
Parameter gen_dim      : Generator -> nat.
Parameter Generator_eq_dec :
  forall g1 g2 : Generator, {g1 = g2} + {g1 <> g2}.

(** ** Raw terms *)
Inductive Term : Type :=
| gen  : Generator -> Term
| src  : Term -> Term
| tgt  : Term -> Term
| id   : Term -> Term
| comp : nat -> Term -> Term -> Term.

(* JW: NEW. Named aliases for iterated source / target / identity.
   These appear in IC11–IC13 (originally written with [Nat.iter] inline)
   and in the boundary premise of the new [wf_comp] in [Axioms.v]. *)
Definition iter_src (k : nat) (t : Term) : Term := Nat.iter k src t.
Definition iter_tgt (k : nat) (t : Term) : Term := Nat.iter k tgt t.
Definition iter_id  (k : nat) (t : Term) : Term := Nat.iter k id  t.

(** ** Dimension
    Partial function on raw terms; [None] marks ill-typed combinations.
    The clauses correspond to D1–D4 of Figure 2:
      D1: dim (src x) = dim x − 1   (when dim x > 0)
      D2: dim (tgt x) = dim x − 1   (when dim x > 0)
      D3: dim (y ∘[n] x) = d        (when dim x = dim y = d > n)
      D4: dim (id x) = dim x + 1                                            *)
Fixpoint dim (t : Term) : option nat :=
  match t with
  | gen g    => Some (gen_dim g)
  | src e    => match dim e with
                | Some (S n) => Some n
                | _          => None
                end
  | tgt e    => match dim e with
                | Some (S n) => Some n
                | _          => None
                end
  | id  e    => match dim e with
                | Some n     => Some (S n)
                | None       => None
                end
  | comp k a b =>
      match dim a, dim b with
      | Some da, Some db =>
          if (da =? db) && (k <? da) then Some da else None
      | _, _ => None
      end
  end.

(* JW: WAS:
   Definition wf (t : Term) : Prop := exists n, dim t = Some n.
   Definition wfb (t : Term) : bool :=
     match dim t with Some _ => true | None => false end.

   The old [wf] was a boundary-blind syntactic check. Per Liron's note,
   [wf] should be an inductive judgment AND should check the boundary
   condition for compositions. The proper [wf] now lives in [Axioms.v]
   (mutual with [eq_cat]). The boolean [wfb] is renamed [dimb] below to
   reflect that it tests only the syntactic [dim], not full well-formedness. *)
Definition dimb (t : Term) : bool :=
  match dim t with Some _ => true | None => false end.

(** ** Dimension lemmas (D1–D4 as computational facts) *)
Lemma dim_gen : forall g, dim (gen g) = Some (gen_dim g).
Proof. reflexivity. Qed.
Lemma dim_src : forall e n,
  dim e = Some (S n) -> dim (src e) = Some n.
Proof. intros e n H; simpl; rewrite H; reflexivity. Qed.
Lemma dim_tgt : forall e n,
  dim e = Some (S n) -> dim (tgt e) = Some n.
Proof. intros e n H; simpl; rewrite H; reflexivity. Qed.
Lemma dim_id : forall e n,
  dim e = Some n -> dim (id e) = Some (S n).
Proof. intros e n H; simpl; rewrite H; reflexivity. Qed.

Lemma dim_comp : forall k a b n,
  dim a = Some n -> dim b = Some n -> k < n ->
  dim (comp k a b) = Some n.
Proof.
  intros k a b n Ha Hb Hk.
  simpl. rewrite Ha, Hb.
  rewrite Nat.eqb_refl; simpl.
  apply Nat.ltb_lt in Hk. rewrite Hk. reflexivity.
Qed.

(** ** Decidable equality on terms *)
Lemma Term_eq_dec : forall t1 t2 : Term, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
  - apply Generator_eq_dec.
  - apply Nat.eq_dec.
Qed.
