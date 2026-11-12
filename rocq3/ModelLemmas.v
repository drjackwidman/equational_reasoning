(** * ModelLemmas.v
    Consequences of the one-step laws of [IsEqCatModel] for iterated
    source, target and identity, over an arbitrary model. These are the
    model-level counterparts of the term-level facts in [Derived.v], and
    are used by [Universal.v] (soundness) and [Strict.v] (adequacy).

    [composable k a b] packages the three facts that [ccomp k a b] takes as
    arguments: equal dimension, k below it, and matching boundary. *)

Require Import Arith PeanoNat Lia.
Require Import Syntax Axioms Meta NormalForm Model FreeModel Decidable Reflect Adequacy.
Require Import Functor.

Lemma iter_shift : forall (A : Type) (f : A -> A) c (x : A),
  Nat.iter (S c) f x = Nat.iter c f (f x).
Proof.
  intros A f. induction c as [|c IH]; intro x; [reflexivity |].
  simpl. simpl in IH. rewrite IH. reflexivity.
Qed.

Section ModelLemmas.
Context (Sg : OmegaSig) (M : IsEqCatModel Sg).

Let sy := ceq_sym Sg M.
Let tr := ceq_trans Sg M.
Let rf := ceq_refl Sg M.

Definition composable (k : nat) (a b : Cell Sg) : Prop :=
  cdim a = cdim b /\ k < cdim a /\
  ceq (Nat.iter (cdim a - k) csrc a) (Nat.iter (cdim a - k) ctgt b).

(** ** Dimensions of iterates *)
Lemma cdim_iter_id : forall c (a : Cell Sg), cdim (Nat.iter c cid a) = cdim a + c.
Proof.
  induction c as [|c IH]; intro a; simpl; [lia |].
  rewrite (cdim_id Sg M), IH. lia.
Qed.

(** ** Iterated operators are congruences *)
Lemma iter_src_ceq : forall c (a b : Cell Sg),
  ceq a b -> c <= cdim a -> ceq (Nat.iter c csrc a) (Nat.iter c csrc b).
Proof.
  induction c as [|c IH]; intros a b H Hc; simpl; [exact H |].
  apply (csrc_ceq Sg M); [| apply IH; [exact H | lia]].
  rewrite (cdim_iter_src Sg M) by lia. lia.
Qed.

Lemma iter_tgt_ceq : forall c (a b : Cell Sg),
  ceq a b -> c <= cdim a -> ceq (Nat.iter c ctgt a) (Nat.iter c ctgt b).
Proof.
  induction c as [|c IH]; intros a b H Hc; simpl; [exact H |].
  apply (ctgt_ceq Sg M); [| apply IH; [exact H | lia]].
  rewrite (cdim_iter_tgt Sg M) by lia. lia.
Qed.

Lemma iter_id_ceq : forall c (a b : Cell Sg),
  ceq a b -> ceq (Nat.iter c cid a) (Nat.iter c cid b).
Proof.
  induction c as [|c IH]; intros a b H; simpl; [exact H |].
  apply (cid_ceq Sg M). apply IH. exact H.
Qed.

(** ** Globularity, iterated *)
Lemma glob_iter_tgt_src : forall c (a : Cell Sg),
  1 <= c -> S c <= cdim a ->
  ceq (Nat.iter c ctgt (csrc a)) (Nat.iter (S c) ctgt a).
Proof.
  induction c as [|c IH]; intros a Hc Hd; [lia |].
  destruct c as [|c].
  - simpl. apply (glob_tgt Sg M). lia.
  - change (ceq (ctgt (Nat.iter (S c) ctgt (csrc a))) (ctgt (Nat.iter (S (S c)) ctgt a))).
    apply (ctgt_ceq Sg M); [| apply IH; lia].
    rewrite (cdim_iter_tgt Sg M) by (rewrite (cdim_src Sg M); lia).
    rewrite (cdim_src Sg M) by lia. lia.
Qed.

Lemma glob_iter_src_tgt : forall c (a : Cell Sg),
  1 <= c -> S c <= cdim a ->
  ceq (Nat.iter c csrc (ctgt a)) (Nat.iter (S c) csrc a).
Proof.
  induction c as [|c IH]; intros a Hc Hd; [lia |].
  destruct c as [|c].
  - simpl. apply sy. apply (glob_src Sg M). lia.
  - change (ceq (csrc (Nat.iter (S c) csrc (ctgt a))) (csrc (Nat.iter (S (S c)) csrc a))).
    apply (csrc_ceq Sg M); [| apply IH; lia].
    rewrite (cdim_iter_src Sg M) by (rewrite (cdim_tgt Sg M); lia).
    rewrite (cdim_tgt Sg M) by lia. lia.
Qed.

(** ** Cancellation of identities *)
Lemma iter_src_id_cancel : forall c (x : Cell Sg),
  ceq (Nat.iter c csrc (Nat.iter c cid x)) x.
Proof.
  induction c as [|c IH]; intro x; [apply rf |].
  rewrite iter_shift. change (Nat.iter (S c) cid x) with (cid (Nat.iter c cid x)).
  apply (tr _ (Nat.iter c csrc (Nat.iter c cid x)) _); [| apply IH].
  apply iter_src_ceq; [apply (src_id Sg M) |].
  rewrite (cdim_src Sg M) by (rewrite (cdim_id Sg M); lia).
  rewrite (cdim_id Sg M), cdim_iter_id. lia.
Qed.

Lemma iter_tgt_id_cancel : forall c (x : Cell Sg),
  ceq (Nat.iter c ctgt (Nat.iter c cid x)) x.
Proof.
  induction c as [|c IH]; intro x; [apply rf |].
  rewrite iter_shift. change (Nat.iter (S c) cid x) with (cid (Nat.iter c cid x)).
  apply (tr _ (Nat.iter c ctgt (Nat.iter c cid x)) _); [| apply IH].
  apply iter_tgt_ceq; [apply (tgt_id Sg M) |].
  rewrite (cdim_tgt Sg M) by (rewrite (cdim_id Sg M); lia).
  rewrite (cdim_id Sg M), cdim_iter_id. lia.
Qed.

(** ** Composability is stable under equality, src, tgt and id *)
Lemma composable_ceq : forall k (a b a' b' : Cell Sg),
  composable k a b -> ceq a a' -> ceq b b' -> composable k a' b'.
Proof.
  intros k a b a' b' (H1 & H2 & H3) Ha Hb.
  pose proof (cdim_ceq Sg M _ _ Ha) as Da. pose proof (cdim_ceq Sg M _ _ Hb) as Db.
  unfold composable. rewrite <- Da, <- Db. split; [exact H1 | split; [exact H2 |]].
  apply (tr _ (Nat.iter (cdim a - k) csrc a) _).
  - apply sy. apply iter_src_ceq; [exact Ha | lia].
  - apply (tr _ (Nat.iter (cdim a - k) ctgt b) _); [exact H3 |].
    apply iter_tgt_ceq; [exact Hb | lia].
Qed.

Lemma composable_src : forall k (a b : Cell Sg),
  composable k a b -> S k < cdim a -> composable k (csrc a) (csrc b).
Proof.
  intros k a b (H1 & H2 & H3) Hk.
  unfold composable. rewrite !(cdim_src Sg M) by lia.
  split; [lia | split; [lia |]].
  remember (cdim a - 1 - k) as c eqn:Ec.
  replace (cdim a - k) with (S c) in H3 by lia.
  rewrite iter_shift in H3.
  apply (tr _ (Nat.iter (S c) ctgt b) _); [exact H3 |].
  apply sy. apply glob_iter_tgt_src; lia.
Qed.

Lemma composable_tgt : forall k (a b : Cell Sg),
  composable k a b -> S k < cdim a -> composable k (ctgt a) (ctgt b).
Proof.
  intros k a b (H1 & H2 & H3) Hk.
  unfold composable. rewrite !(cdim_tgt Sg M) by lia.
  split; [lia | split; [lia |]].
  remember (cdim a - 1 - k) as c eqn:Ec.
  replace (cdim a - k) with (S c) in H3 by lia.
  rewrite (iter_shift _ ctgt c b) in H3.
  apply (tr _ (Nat.iter (S c) csrc a) _); [| exact H3].
  apply glob_iter_src_tgt; lia.
Qed.

Lemma composable_id : forall k (a b : Cell Sg),
  composable k a b -> composable k (cid a) (cid b).
Proof.
  intros k a b (H1 & H2 & H3).
  unfold composable. rewrite !(cdim_id Sg M).
  split; [lia | split; [lia |]].
  replace (S (cdim a) - k) with (S (cdim a - k)) by lia.
  rewrite !iter_shift.
  apply (tr _ (Nat.iter (cdim a - k) csrc a) _).
  { apply iter_src_ceq; [apply (src_id Sg M) |].
    rewrite (cdim_src Sg M) by (rewrite (cdim_id Sg M); lia).
    rewrite (cdim_id Sg M). lia. }
  apply (tr _ (Nat.iter (cdim a - k) ctgt b) _); [exact H3 |].
  apply sy. apply iter_tgt_ceq; [apply (tgt_id Sg M) |].
  rewrite (cdim_tgt Sg M) by (rewrite (cdim_id Sg M); lia).
  rewrite (cdim_id Sg M). lia.
Qed.

Lemma composable_src_iter : forall j k (a b : Cell Sg),
  composable k a b -> k + j < cdim a ->
  composable k (Nat.iter j csrc a) (Nat.iter j csrc b).
Proof.
  induction j as [|j IH]; intros k a b H Hj; [exact H |].
  simpl. apply composable_src; [apply IH; [exact H | lia] |].
  rewrite (cdim_iter_src Sg M) by lia. lia.
Qed.

Lemma composable_tgt_iter : forall j k (a b : Cell Sg),
  composable k a b -> k + j < cdim a ->
  composable k (Nat.iter j ctgt a) (Nat.iter j ctgt b).
Proof.
  induction j as [|j IH]; intros k a b H Hj; [exact H |].
  simpl. apply composable_tgt; [apply IH; [exact H | lia] |].
  rewrite (cdim_iter_tgt Sg M) by lia. lia.
Qed.

Lemma composable_id_iter : forall j k (a b : Cell Sg),
  composable k a b -> composable k (Nat.iter j cid a) (Nat.iter j cid b).
Proof.
  induction j as [|j IH]; intros k a b H; [exact H |].
  simpl. apply composable_id. apply IH. exact H.
Qed.

(** ** Iterated source and target of a composite, below the gluing level:
       src^j (a ∘_k b) = src^j a ∘_k src^j b for k + j < dim. *)
Lemma src_comp_low_iter : forall j k (a b : Cell Sg) H1 H2 H3 H1' H2' H3',
  k + j < cdim a ->
  ceq (Nat.iter j csrc (ccomp k a b H1 H2 H3))
      (ccomp k (Nat.iter j csrc a) (Nat.iter j csrc b) H1' H2' H3').
Proof.
  induction j as [|j IH]; intros k a b H1 H2 H3 H1' H2' H3' Hj.
  - simpl. apply (ccomp_ceq Sg M); apply rf.
  - destruct (composable_src_iter j k a b (conj H1 (conj H2 H3)) ltac:(lia)) as (P1 & P2 & P3).
    simpl.
    apply (tr _ (csrc (ccomp k (Nat.iter j csrc a) (Nat.iter j csrc b) P1 P2 P3)) _).
    + apply (csrc_ceq Sg M); [| apply IH; lia].
      rewrite (cdim_iter_src Sg M) by (rewrite (cdim_comp Sg M); lia).
      rewrite (cdim_comp Sg M). lia.
    + apply (src_comp_low Sg M). rewrite (cdim_iter_src Sg M) by lia. lia.
Qed.

Lemma tgt_comp_low_iter : forall j k (a b : Cell Sg) H1 H2 H3 H1' H2' H3',
  k + j < cdim a ->
  ceq (Nat.iter j ctgt (ccomp k a b H1 H2 H3))
      (ccomp k (Nat.iter j ctgt a) (Nat.iter j ctgt b) H1' H2' H3').
Proof.
  induction j as [|j IH]; intros k a b H1 H2 H3 H1' H2' H3' Hj.
  - simpl. apply (ccomp_ceq Sg M); apply rf.
  - destruct (composable_tgt_iter j k a b (conj H1 (conj H2 H3)) ltac:(lia)) as (P1 & P2 & P3).
    simpl.
    apply (tr _ (ctgt (ccomp k (Nat.iter j ctgt a) (Nat.iter j ctgt b) P1 P2 P3)) _).
    + apply (ctgt_ceq Sg M); [| apply IH; lia].
      rewrite (cdim_iter_tgt Sg M) by (rewrite (cdim_comp Sg M); lia).
      rewrite (cdim_comp Sg M). lia.
    + apply (tgt_comp_low Sg M). rewrite (cdim_iter_tgt Sg M) by lia. lia.
Qed.

(** id^j (a ∘_k b) = id^j a ∘_k id^j b. *)
Lemma id_comp_iter : forall j k (a b : Cell Sg) H1 H2 H3 H1' H2' H3',
  ceq (Nat.iter j cid (ccomp k a b H1 H2 H3))
      (ccomp k (Nat.iter j cid a) (Nat.iter j cid b) H1' H2' H3').
Proof.
  induction j as [|j IH]; intros k a b H1 H2 H3 H1' H2' H3'.
  - simpl. apply (ccomp_ceq Sg M); apply rf.
  - destruct (composable_id_iter j k a b (conj H1 (conj H2 H3))) as (P1 & P2 & P3).
    simpl.
    apply (tr _ (cid (ccomp k (Nat.iter j cid a) (Nat.iter j cid b) P1 P2 P3)) _).
    + apply (cid_ceq Sg M). apply IH.
    + apply (id_comp Sg M).
Qed.

(** ** Iterated source and target of a composite, down to the gluing level:
       src^c (a ∘_k b) = src^c b and tgt^c (a ∘_k b) = tgt^c a for
       dim = k + c. *)
Lemma src_comp_top_iter : forall c k (a b : Cell Sg) H1 H2 H3,
  1 <= c -> cdim a = k + c ->
  ceq (Nat.iter c csrc (ccomp k a b H1 H2 H3)) (Nat.iter c csrc b).
Proof.
  intros c k a b H1 H2 H3 Hc Hd.
  destruct c as [|c]; [lia |].
  destruct (composable_src_iter c k a b (conj H1 (conj H2 H3)) ltac:(lia)) as (P1 & P2 & P3).
  simpl.
  apply (tr _ (csrc (ccomp k (Nat.iter c csrc a) (Nat.iter c csrc b) P1 P2 P3)) _).
  - apply (csrc_ceq Sg M); [| apply src_comp_low_iter; lia].
    rewrite (cdim_iter_src Sg M) by (rewrite (cdim_comp Sg M); lia).
    rewrite (cdim_comp Sg M). lia.
  - apply (src_comp_top Sg M). rewrite (cdim_iter_src Sg M) by lia. lia.
Qed.

Lemma tgt_comp_top_iter : forall c k (a b : Cell Sg) H1 H2 H3,
  1 <= c -> cdim a = k + c ->
  ceq (Nat.iter c ctgt (ccomp k a b H1 H2 H3)) (Nat.iter c ctgt a).
Proof.
  intros c k a b H1 H2 H3 Hc Hd.
  destruct c as [|c]; [lia |].
  destruct (composable_tgt_iter c k a b (conj H1 (conj H2 H3)) ltac:(lia)) as (P1 & P2 & P3).
  simpl.
  apply (tr _ (ctgt (ccomp k (Nat.iter c ctgt a) (Nat.iter c ctgt b) P1 P2 P3)) _).
  - apply (ctgt_ceq Sg M); [| apply tgt_comp_low_iter; lia].
    rewrite (cdim_iter_tgt Sg M) by (rewrite (cdim_comp Sg M); lia).
    rewrite (cdim_comp Sg M). lia.
  - apply (tgt_comp_top Sg M). rewrite (cdim_iter_tgt Sg M) by lia. lia.
Qed.

End ModelLemmas.
