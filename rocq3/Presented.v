(** * Presented.v
    EqCat∞ over generators with declared boundaries.

    [Axioms.v] treats the free model on a stratified set: a generator has a
    dimension and nothing else, so two distinct generators never compose.
    Here a generator may also declare its source and target (as terms over
    the lower generators). The axioms of Figure 2 are unchanged; the only
    additions are the two boundary equations [B_src], [B_tgt] and the
    typing rule [wf_genB] for a generator with a declared boundary.

    With no declarations the rules coincide with those of [Axioms.v]
    (read off the constructors; the equivalence is not proved here).

    Convention as in [Axioms.v]: [comp k a b] is [a ∘_k b], well-formed at
    dimension [n] when [src^{n-k} a == tgt^{n-k} b]. *)

Require Import Arith Lia.
Require Import Syntax.

(** ** Boundary declarations over a generating set. *)
Module Type BDY (G : GEN).
  Module Syn := SyntaxF G.
  Parameter gen_bd : G.Generator -> option (Syn.Term * Syn.Term).
End BDY.

Module PresentedF (G : GEN) (B : BDY G).
Include B.Syn.
Definition gen_bd := B.gen_bd.

Reserved Notation "a == b" (at level 70, no associativity).

Inductive wf : Term -> nat -> Prop :=
(** A generator with no declared boundary, as in [Axioms.v]. *)
| wf_gen0 :
    forall g, gen_bd g = None -> wf (gen g) (gen_dim g)
(** A generator with declared boundary [s], [t]: both must be well-formed
    one dimension down. *)
| wf_genB :
    forall g s t n,
      gen_bd g = Some (s, t) -> gen_dim g = S n ->
      wf s n -> wf t n ->
      wf (gen g) (S n)
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

(** ** Declared boundaries *)
| B_src :
    forall g s t n,
      gen_bd g = Some (s, t) -> wf (gen g) (S n) -> src (gen g) == s
| B_tgt :
    forall g s t n,
      gen_bd g = Some (s, t) -> wf (gen g) (S n) -> tgt (gen g) == t

(** ** Structural equality axioms (E1–E8), verbatim from [Axioms.v] *)
| E1_refl :
    forall x, x == x
| E2_sym :
    forall x y, x == y -> y == x
| E3_trans :
    forall x y z, x == y -> y == z -> x == z
| E5_src :
    forall x y n,
      x == y -> wf x (S n) -> wf y (S n) ->
      src x == src y
| E6_tgt :
    forall x y n,
      x == y -> wf x (S n) -> wf y (S n) ->
      tgt x == tgt y
| E7_comp :
    forall x y z w n d,
      x == y -> z == w ->
      wf (comp n x z) d -> wf (comp n y w) d ->
      comp n x z == comp n y w
| E8_id :
    forall x y, x == y -> id x == id y

(** ** ∞-categorical axioms (IC1–IC13), verbatim from [Axioms.v] *)
| IC1 :
    forall x n,
      wf x n -> n >= 2 ->
      src (src x) == src (tgt x)
| IC2 :
    forall x n,
      wf x n -> n >= 2 ->
      tgt (src x) == tgt (tgt x)
| IC3 :
    forall x n, wf x n -> src (id x) == x
| IC4 :
    forall x n, wf x n -> tgt (id x) == x
| IC5 :
    forall x y n,
      wf (comp n y x) (S n) ->
      src (comp n y x) == src x
| IC6 :
    forall x y n,
      wf (comp n y x) (S n) ->
      tgt (comp n y x) == tgt y
| IC7 :
    forall x y n d,
      wf (comp n y x) d -> d > S n ->
      src (comp n y x) == comp n (src y) (src x)
| IC8 :
    forall x y n d,
      wf (comp n y x) d -> d > S n ->
      tgt (comp n y x) == comp n (tgt y) (tgt x)
| IC9 :
    forall x y z n d,
      wf (comp n (comp n x y) z) d ->
      wf (comp n x (comp n y z)) d ->
      comp n (comp n x y) z == comp n x (comp n y z)
| IC10 :
    forall x y z w m n d,
      wf (comp m (comp n x y) (comp n z w)) d ->
      wf (comp n (comp m x z) (comp m y w)) d ->
      comp m (comp n x y) (comp n z w) ==
      comp n (comp m x z) (comp m y w)
| IC11 :
    forall x n d,
      wf x d -> d > n ->
      wf (comp n x (iter_id (d - n) (iter_src (d - n) x))) d ->
      comp n x (iter_id (d - n) (iter_src (d - n) x)) == x
| IC12 :
    forall x n d,
      wf x d -> d > n ->
      wf (comp n (iter_id (d - n) (iter_tgt (d - n) x)) x) d ->
      comp n (iter_id (d - n) (iter_tgt (d - n) x)) x == x
| IC13 :
    forall x y n d,
      wf (comp n y x) d -> d > n ->
      id (comp n y x) == comp n (id y) (id x)

where "a == b" := (eq_cat a b).

(** ** Small tactics for chaining equations and unary well-formedness. *)
Ltac tr y := apply (E3_trans _ y _).
Ltac sy := apply E2_sym.
Ltac wfs := repeat first [eassumption | apply wf_id | apply wf_src | apply wf_tgt].

(** ** Two sources (targets) strip two identities. *)
Lemma ss_id : forall y n, wf y n -> src (src (id (id y))) == y.
Proof.
  intros y n H. tr (src (id y)).
  - apply (E5_src _ _ n); [apply (IC3 (id y) (S n)) | |]; wfs.
  - apply (IC3 y n H).
Qed.

Lemma tt_id : forall y n, wf y n -> tgt (tgt (id (id y))) == y.
Proof.
  intros y n H. tr (tgt (id y)).
  - apply (E6_tgt _ _ n); [apply (IC4 (id y) (S n)) | |]; wfs.
  - apply (IC4 y n H).
Qed.

Lemma ts_id : forall y n, wf y n -> tgt (src (id (id y))) == y.
Proof.
  intros y n H. tr (tgt (id y)).
  - apply (E6_tgt _ _ n); [apply (IC3 (id y) (S n)) | |]; wfs.
  - apply (IC4 y n H).
Qed.

Lemma st_id : forall y n, wf y n -> src (tgt (id (id y))) == y.
Proof.
  intros y n H. tr (src (id y)).
  - apply (E5_src _ _ n); [apply (IC4 (id y) (S n)) | |]; wfs.
  - apply (IC3 y n H).
Qed.

End PresentedF.
