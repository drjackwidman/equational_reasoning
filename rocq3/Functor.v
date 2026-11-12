(** * Functor.v
    ∞-functors and ∞-natural transformations between models of EqCat∞
    (Section 2.4 of the paper), over the abstract signature [OmegaSig] and
    the laws [IsEqCatModel] of [Adequacy.v].

    Contents:
      - one-step consequences of the model laws used here and in
        [Inverse.v]: [cdim_iter_src], [cdim_iter_tgt], [comp1_ok],
        [unit_r1], [unit_l1];
      - [IsFunctor], with [fun_composable] (a functor sends composable
        pairs to composable pairs, so the right-hand side of the
        composition law exists), the typing rule [fun_typing], and the
        identity functor [id_functor];
      - [IsNatTrans], with [nt_composable] (both sides of the naturality
        square exist) and the identity transformation [id_nat_trans].

    Composition in [OmegaSig] takes proofs of composability as arguments.
    Laws that mention a composite are stated for every choice of those
    proofs, as in [IsEqCatModel]. *)

Require Import Arith PeanoNat Lia.
Require Import Syntax Axioms Meta NormalForm Model FreeModel Decidable Reflect Adequacy.

(** ** 1. One-step consequences of the model laws *)
Section ModelFacts.
Context (Sg : OmegaSig) (M : IsEqCatModel Sg).

Lemma cdim_iter_src : forall c (a : Cell Sg),
  c <= cdim a -> cdim (Nat.iter c csrc a) = cdim a - c.
Proof.
  induction c as [|c IH]; intros a Hc; simpl.
  - lia.
  - rewrite (cdim_src Sg M) by (rewrite IH; lia). rewrite IH by lia. lia.
Qed.

Lemma cdim_iter_tgt : forall c (a : Cell Sg),
  c <= cdim a -> cdim (Nat.iter c ctgt a) = cdim a - c.
Proof.
  induction c as [|c IH]; intros a Hc; simpl.
  - lia.
  - rewrite (cdim_tgt Sg M) by (rewrite IH; lia). rewrite IH by lia. lia.
Qed.

(** Composability data for two cells of dimension k+1 glued along their
    common k-dimensional boundary. *)
Lemma comp1_ok : forall k (x y : Cell Sg),
  cdim x = S k -> cdim y = S k -> ceq (csrc x) (ctgt y) ->
  cdim x = cdim y /\ k < cdim x /\
  ceq (Nat.iter (cdim x - k) csrc x) (Nat.iter (cdim x - k) ctgt y).
Proof.
  intros k x y Hx Hy H. split; [lia | split; [lia |]].
  replace (cdim x - k) with 1 by lia. exact H.
Qed.

Lemma cdim_id_src : forall k (a : Cell Sg), cdim a = S k -> cdim (cid (csrc a)) = S k.
Proof. intros k a H. rewrite (cdim_id Sg M), (cdim_src Sg M) by lia. lia. Qed.

Lemma cdim_id_tgt : forall k (a : Cell Sg), cdim a = S k -> cdim (cid (ctgt a)) = S k.
Proof. intros k a H. rewrite (cdim_id Sg M), (cdim_tgt Sg M) by lia. lia. Qed.

(** Right unit law in codimension one: a ∘_k id (src a) = a. *)
Lemma unit_r1 : forall k (a : Cell Sg), cdim a = S k ->
  forall H1 H2 H3, ceq (ccomp k a (cid (csrc a)) H1 H2 H3) a.
Proof.
  intros k a Hd.
  assert (X : cidext_src (cdim a - k) a = cid (csrc a))
    by (unfold cidext_src; replace (cdim a - k) with 1 by lia; reflexivity).
  pose proof (unit_r Sg M k a) as U. rewrite X in U. exact U.
Qed.

(** Left unit law in codimension one: id (tgt a) ∘_k a = a. *)
Lemma unit_l1 : forall k (a : Cell Sg), cdim a = S k ->
  forall H1 H2 H3, ceq (ccomp k (cid (ctgt a)) a H1 H2 H3) a.
Proof.
  intros k a Hd.
  assert (X : cidext_tgt (cdim a - k) a = cid (ctgt a))
    by (unfold cidext_tgt; replace (cdim a - k) with 1 by lia; reflexivity).
  pose proof (unit_l Sg M k a) as U. rewrite X in U. exact U.
Qed.

(** The same with the identity taken on any cell equal to the boundary. *)
Lemma unit_r1' : forall k (a x : Cell Sg), cdim a = S k -> ceq x (csrc a) ->
  forall H1 H2 H3, ceq (ccomp k a (cid x) H1 H2 H3) a.
Proof.
  intros k a x Hd Hx H1 H2 H3.
  destruct (comp1_ok k a (cid (csrc a)) Hd (cdim_id_src k a Hd)
              (ceq_sym Sg M _ _ (tgt_id Sg M (csrc a)))) as (P1 & P2 & P3).
  apply (ceq_trans Sg M _ (ccomp k a (cid (csrc a)) P1 P2 P3) _).
  - apply (ccomp_ceq Sg M); [apply (ceq_refl Sg M) | apply (cid_ceq Sg M); exact Hx].
  - apply unit_r1; exact Hd.
Qed.

Lemma unit_l1' : forall k (a x : Cell Sg), cdim a = S k -> ceq x (ctgt a) ->
  forall H1 H2 H3, ceq (ccomp k (cid x) a H1 H2 H3) a.
Proof.
  intros k a x Hd Hx H1 H2 H3.
  destruct (comp1_ok k (cid (ctgt a)) a (cdim_id_tgt k a Hd) Hd
              (src_id Sg M (ctgt a))) as (P1 & P2 & P3).
  apply (ceq_trans Sg M _ (ccomp k (cid (ctgt a)) a P1 P2 P3) _).
  - apply (ccomp_ceq Sg M); [apply (cid_ceq Sg M); exact Hx | apply (ceq_refl Sg M)].
  - apply unit_l1; exact Hd.
Qed.

End ModelFacts.

(** ** 2. ∞-functors *)

(** An ∞-functor F : C -> D is a map on cells that respects equality,
    preserves dimension, commutes with source and target, and respects
    composition and identities. *)
Record IsFunctor (C D : OmegaSig) (F : Cell C -> Cell D) : Prop := {
  fun_ceq  : forall a b : Cell C, ceq a b -> ceq (F a) (F b);
  fun_dim  : forall a : Cell C, cdim (F a) = cdim a;
  fun_src  : forall a : Cell C, cdim a > 0 -> ceq (csrc (F a)) (F (csrc a));
  fun_tgt  : forall a : Cell C, cdim a > 0 -> ceq (ctgt (F a)) (F (ctgt a));
  fun_comp : forall (k : nat) (a b : Cell C) H1 H2 H3 H1' H2' H3',
      ceq (F (ccomp k a b H1 H2 H3)) (ccomp k (F a) (F b) H1' H2' H3');
  fun_id   : forall a : Cell C, ceq (F (cid a)) (cid (F a))
}.

Section FunctorFacts.
Context (C D : OmegaSig) (MC : IsEqCatModel C) (MD : IsEqCatModel D).
Context (F : Cell C -> Cell D) (HF : IsFunctor C D F).

Lemma fun_iter_src : forall c (a : Cell C), c <= cdim a ->
  ceq (Nat.iter c csrc (F a)) (F (Nat.iter c csrc a)).
Proof.
  induction c as [|c IH]; intros a Hc; simpl.
  - apply (ceq_refl D MD).
  - apply (ceq_trans D MD _ (csrc (F (Nat.iter c csrc a))) _).
    + apply (csrc_ceq D MD); [| apply IH; lia].
      rewrite (cdim_iter_src D MD) by (rewrite (fun_dim C D F HF); lia).
      rewrite (fun_dim C D F HF). lia.
    + apply (fun_src C D F HF). rewrite (cdim_iter_src C MC) by lia. lia.
Qed.

Lemma fun_iter_tgt : forall c (a : Cell C), c <= cdim a ->
  ceq (Nat.iter c ctgt (F a)) (F (Nat.iter c ctgt a)).
Proof.
  induction c as [|c IH]; intros a Hc; simpl.
  - apply (ceq_refl D MD).
  - apply (ceq_trans D MD _ (ctgt (F (Nat.iter c ctgt a))) _).
    + apply (ctgt_ceq D MD); [| apply IH; lia].
      rewrite (cdim_iter_tgt D MD) by (rewrite (fun_dim C D F HF); lia).
      rewrite (fun_dim C D F HF). lia.
    + apply (fun_tgt C D F HF). rewrite (cdim_iter_tgt C MC) by lia. lia.
Qed.

(** A functor sends composable pairs to composable pairs. So for every
    composite a ∘_k b in C the composite F a ∘_k F b exists in D, and
    [fun_comp] is a statement about an existing cell. *)
Theorem fun_composable : forall k (a b : Cell C),
  cdim a = cdim b -> k < cdim a ->
  ceq (Nat.iter (cdim a - k) csrc a) (Nat.iter (cdim a - k) ctgt b) ->
  cdim (F a) = cdim (F b) /\ k < cdim (F a) /\
  ceq (Nat.iter (cdim (F a) - k) csrc (F a)) (Nat.iter (cdim (F a) - k) ctgt (F b)).
Proof.
  intros k a b H1 H2 H3.
  rewrite !(fun_dim C D F HF). split; [exact H1 | split; [exact H2 |]].
  apply (ceq_trans D MD _ (F (Nat.iter (cdim a - k) csrc a)) _).
  - apply fun_iter_src. lia.
  - apply (ceq_trans D MD _ (F (Nat.iter (cdim a - k) ctgt b)) _).
    + apply (fun_ceq C D F HF). exact H3.
    + apply (ceq_sym D MD). apply fun_iter_tgt. lia.
Qed.

(** The typing rule: f : a -> b gives F f : F a -> F b. *)
Theorem fun_typing : forall f a b : Cell C,
  cdim f > 0 -> ceq (csrc f) a -> ceq (ctgt f) b ->
  ceq (csrc (F f)) (F a) /\ ceq (ctgt (F f)) (F b).
Proof.
  intros f a b Hd Ha Hb. split.
  - apply (ceq_trans D MD _ (F (csrc f)) _);
      [apply (fun_src C D F HF); exact Hd | apply (fun_ceq C D F HF); exact Ha].
  - apply (ceq_trans D MD _ (F (ctgt f)) _);
      [apply (fun_tgt C D F HF); exact Hd | apply (fun_ceq C D F HF); exact Hb].
Qed.

End FunctorFacts.

(** The identity map is a functor. *)
Theorem id_functor : forall (C : OmegaSig), IsEqCatModel C ->
  IsFunctor C C (fun a => a).
Proof.
  intros C MC. constructor; intros.
  - assumption.
  - reflexivity.
  - apply (ceq_refl C MC).
  - apply (ceq_refl C MC).
  - apply (ccomp_ceq C MC); apply (ceq_refl C MC).
  - apply (ceq_refl C MC).
Qed.

(** ** 3. ∞-natural transformations *)

(** A natural transformation phi : F -> G assigns to each cell a of
    dimension k a cell phi a : F a -> G a of dimension k+1, such that for
    every f : a -> b of dimension k+1,
        G f ∘_k phi a  =  phi b ∘_k F f. *)
Record IsNatTrans (C D : OmegaSig) (F G phi : Cell C -> Cell D) : Prop := {
  nt_ceq : forall a b : Cell C, ceq a b -> ceq (phi a) (phi b);
  nt_dim : forall a : Cell C, cdim (phi a) = S (cdim a);
  nt_src : forall a : Cell C, ceq (csrc (phi a)) (F a);
  nt_tgt : forall a : Cell C, ceq (ctgt (phi a)) (G a);
  nt_natural : forall (k : nat) (f : Cell C), cdim f = S k ->
      forall H1 H2 H3 H1' H2' H3',
      ceq (ccomp k (G f) (phi (csrc f)) H1 H2 H3)
          (ccomp k (phi (ctgt f)) (F f) H1' H2' H3')
}.

Section NatTransFacts.
Context (C D : OmegaSig) (MC : IsEqCatModel C) (MD : IsEqCatModel D).
Context (F G : Cell C -> Cell D) (HF : IsFunctor C D F) (HG : IsFunctor C D G).

(** Both sides of the naturality square exist, given only the typing of
    phi. So [nt_natural] is a statement about existing cells. *)
Theorem nt_composable : forall (phi : Cell C -> Cell D),
  (forall a, cdim (phi a) = S (cdim a)) ->
  (forall a, ceq (csrc (phi a)) (F a)) ->
  (forall a, ceq (ctgt (phi a)) (G a)) ->
  forall k (f : Cell C), cdim f = S k ->
  (cdim (G f) = cdim (phi (csrc f)) /\ k < cdim (G f) /\
   ceq (Nat.iter (cdim (G f) - k) csrc (G f))
       (Nat.iter (cdim (G f) - k) ctgt (phi (csrc f))))
  /\
  (cdim (phi (ctgt f)) = cdim (F f) /\ k < cdim (phi (ctgt f)) /\
   ceq (Nat.iter (cdim (phi (ctgt f)) - k) csrc (phi (ctgt f)))
       (Nat.iter (cdim (phi (ctgt f)) - k) ctgt (F f))).
Proof.
  intros phi Hd Hs Ht k f Hf.
  assert (Dsf : cdim (csrc f) = k) by (rewrite (cdim_src C MC); lia).
  assert (Dtf : cdim (ctgt f) = k) by (rewrite (cdim_tgt C MC); lia).
  split.
  - apply (comp1_ok D k).
    + rewrite (fun_dim C D G HG). exact Hf.
    + rewrite Hd, Dsf. reflexivity.
    + apply (ceq_trans D MD _ (G (csrc f)) _).
      * apply (fun_src C D G HG). lia.
      * apply (ceq_sym D MD). apply Ht.
  - apply (comp1_ok D k).
    + rewrite Hd, Dtf. reflexivity.
    + rewrite (fun_dim C D F HF). exact Hf.
    + apply (ceq_trans D MD _ (F (ctgt f)) _).
      * apply Hs.
      * apply (ceq_sym D MD). apply (fun_tgt C D F HF). lia.
Qed.

(** The identity transformation F -> F, with components id (F a). *)
Theorem id_nat_trans : IsNatTrans C D F F (fun a => cid (F a)).
Proof.
  constructor.
  - intros a b H. apply (cid_ceq D MD). apply (fun_ceq C D F HF). exact H.
  - intro a. rewrite (cdim_id D MD), (fun_dim C D F HF). reflexivity.
  - intro a. apply (src_id D MD).
  - intro a. apply (tgt_id D MD).
  - intros k f Hf H1 H2 H3 H1' H2' H3'.
    assert (DF : cdim (F f) = S k) by (rewrite (fun_dim C D F HF); exact Hf).
    apply (ceq_trans D MD _ (F f) _).
    + apply (unit_r1' D MD k (F f) (F (csrc f)) DF).
      apply (ceq_sym D MD). apply (fun_src C D F HF). lia.
    + apply (ceq_sym D MD).
      apply (unit_l1' D MD k (F f) (F (ctgt f)) DF).
      apply (ceq_sym D MD). apply (fun_tgt C D F HF). lia.
Qed.

End NatTransFacts.

Print Assumptions fun_composable.
Print Assumptions id_nat_trans.
