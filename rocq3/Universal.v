(** * Universal.v
    Interpretation of terms in an arbitrary model, soundness of the
    calculus, and the universal property of the free model.

    Fix a model (an [OmegaSig] satisfying [IsEqCatModel]) and a
    dimension-preserving assignment [sigma] of its cells to the generators.

      - [Interp t c]: the term t is defined under sigma and denotes c.
        This is the partial function of the paper's semantics, as a
        relation: a composite is defined exactly when its operands are
        and their boundaries match in the model.
      - [soundness]: provably equal terms are defined together and denote
        equal cells; every well-formed term is defined.
      - [ext]: the resulting map from the free model to the model. It is
        an ∞-functor ([ext_functor]), extends sigma ([ext_gen]), and is
        the only functor that does ([ext_unique]).

    The last three say that the free model is free on its stratified set
    of generators. The categories of models and of stratified sets, and
    the adjunction between them, are not formalized; this is the
    universal property that the adjunction amounts to. *)

Require Import Arith PeanoNat Lia.
Require Import Syntax Axioms Meta NormalForm Model FreeModel Decidable Reflect Adequacy.
Require Import Functor ModelLemmas Strict.

Module UniversalF (G : GEN).
Include AdequacyF G.

Section Interpretation.
Context (Sg : OmegaSig) (M : IsEqCatModel Sg).
Context (sigma : Generator -> Cell Sg).
Context (Hsig : forall g, cdim (sigma g) = gen_dim g).

Let sy := ceq_sym Sg M.
Let tr := ceq_trans Sg M.
Let rf := ceq_refl Sg M.

(** ** 1. Interpretation *)
Inductive Interp : Term -> Cell Sg -> Prop :=
| I_gen  : forall g, Interp (gen g) (sigma g)
| I_src  : forall e x, Interp e x -> cdim x > 0 -> Interp (src e) (csrc x)
| I_tgt  : forall e x, Interp e x -> cdim x > 0 -> Interp (tgt e) (ctgt x)
| I_id   : forall e x, Interp e x -> Interp (id e) (cid x)
| I_comp : forall k a b x y H1 H2 H3,
    Interp a x -> Interp b y -> Interp (comp k a b) (ccomp k x y H1 H2 H3).

(** A term is defined under sigma if it denotes some cell. *)
Definition defined (t : Term) : Prop := exists c, Interp t c.

(** The denotation is unique up to the equality of the model. *)
Lemma Interp_fun : forall t x, Interp t x -> forall y, Interp t y -> ceq x y.
Proof.
  induction 1 as [g | e x Hx IH Hd | e x Hx IH Hd | e x Hx IH
                  | k a b x y H1 H2 H3 Hx IHx Hy IHy]; intros z Hz; inversion Hz; subst.
  - apply rf.
  - apply (csrc_ceq Sg M); [exact Hd | apply IH; assumption].
  - apply (ctgt_ceq Sg M); [exact Hd | apply IH; assumption].
  - apply (cid_ceq Sg M). apply IH; assumption.
  - apply (ccomp_ceq Sg M); [apply IHx | apply IHy]; assumption.
Qed.

(** The dimension of the denotation is the syntactic dimension. *)
Lemma Interp_dim : forall t x, Interp t x -> dim t = Some (cdim x).
Proof.
  induction 1 as [g | e x Hx IH Hd | e x Hx IH Hd | e x Hx IH
                  | k a b x y H1 H2 H3 Hx IHx Hy IHy].
  - simpl. rewrite Hsig. reflexivity.
  - apply dim_src. rewrite IH. f_equal. rewrite (cdim_src Sg M) by exact Hd. lia.
  - apply dim_tgt. rewrite IH. f_equal. rewrite (cdim_tgt Sg M) by exact Hd. lia.
  - rewrite (cdim_id Sg M). apply dim_id. exact IH.
  - rewrite (cdim_comp Sg M). apply dim_comp; [exact IHx | rewrite IHy, H1; reflexivity | exact H2].
Qed.

Lemma Interp_wf_dim : forall t x d, Interp t x -> wf t d -> cdim x = d.
Proof.
  intros t x d Hi Hw. apply Interp_dim in Hi. apply wf_dim_sound in Hw.
  rewrite Hw in Hi. injection Hi; auto.
Qed.

(** Iterated operators. *)
Lemma Interp_iter_src : forall c t x, Interp t x -> c <= cdim x ->
  Interp (iter_src c t) (Nat.iter c csrc x).
Proof.
  induction c as [|c IH]; intros t x H Hc; [exact H |].
  change (iter_src (S c) t) with (src (iter_src c t)). simpl.
  apply I_src; [apply IH; [exact H | lia] |].
  rewrite (cdim_iter_src Sg M) by lia. lia.
Qed.

Lemma Interp_iter_tgt : forall c t x, Interp t x -> c <= cdim x ->
  Interp (iter_tgt c t) (Nat.iter c ctgt x).
Proof.
  induction c as [|c IH]; intros t x H Hc; [exact H |].
  change (iter_tgt (S c) t) with (tgt (iter_tgt c t)). simpl.
  apply I_tgt; [apply IH; [exact H | lia] |].
  rewrite (cdim_iter_tgt Sg M) by lia. lia.
Qed.

Lemma Interp_iter_id : forall c t x, Interp t x ->
  Interp (iter_id c t) (Nat.iter c cid x).
Proof.
  induction c as [|c IH]; intros t x H; [exact H |].
  change (iter_id (S c) t) with (id (iter_id c t)). simpl.
  apply I_id. apply IH. exact H.
Qed.

(** ** 2. Soundness *)

(** [same t t']: t and t' are defined together, with equal denotations. *)
Definition same (t t' : Term) : Prop :=
  (forall c, Interp t c -> exists c', Interp t' c' /\ ceq c c') /\
  (forall c', Interp t' c' -> exists c, Interp t c /\ ceq c c').

(** [den t d]: t is defined and its denotation has dimension d. *)
Definition den (t : Term) (d : nat) : Prop := exists c, Interp t c /\ cdim c = d.

Lemma same_of_defined : forall t t' c c',
  Interp t c -> Interp t' c' -> ceq c c' -> same t t'.
Proof.
  intros t t' c c' H H' E. split.
  - intros x Hx. exists c'. split; [exact H' |].
    apply (tr _ c _); [apply (Interp_fun t x Hx c H) | exact E].
  - intros x Hx. exists c. split; [exact H |].
    apply (tr _ c' _); [exact E | apply (Interp_fun t' c' H' x Hx)].
Qed.

Lemma same_sym : forall t t', same t t' -> same t' t.
Proof.
  intros t t' [H1 H2]. split.
  - intros c Hc. destruct (H2 c Hc) as (x & Hx & E). exists x. split; [exact Hx | apply sy; exact E].
  - intros c Hc. destruct (H1 c Hc) as (x & Hx & E). exists x. split; [exact Hx | apply sy; exact E].
Qed.

Lemma same_trans : forall t t' t'', same t t' -> same t' t'' -> same t t''.
Proof.
  intros t t' t'' [A1 A2] [B1 B2]. split.
  - intros c Hc. destruct (A1 c Hc) as (x & Hx & E). destruct (B1 x Hx) as (y & Hy & E').
    exists y. split; [exact Hy | apply (tr _ x _); assumption].
  - intros c Hc. destruct (B2 c Hc) as (x & Hx & E). destruct (A2 x Hx) as (y & Hy & E').
    exists y. split; [exact Hy | apply (tr _ x _); assumption].
Qed.

Lemma same_src : forall t t', same t t' -> same (src t) (src t').
Proof.
  assert (K : forall t t', (forall c, Interp t c -> exists c', Interp t' c' /\ ceq c c') ->
              forall c, Interp (src t) c -> exists c', Interp (src t') c' /\ ceq c c').
  { intros t t' H c Hc. inversion Hc; subst.
    destruct (H x H1) as (y & Hy & E).
    exists (csrc y). split.
    - apply I_src; [exact Hy | rewrite <- (cdim_ceq Sg M _ _ E); assumption].
    - apply (csrc_ceq Sg M); assumption. }
  intros t t' S. pose proof (same_sym _ _ S) as S'. destruct S as [S1 _], S' as [S2 _].
  split; [apply K; exact S1 |].
  intros c Hc. destruct (K t' t S2 c Hc) as (x & Hx & E).
  exists x. split; [exact Hx | apply sy; exact E].
Qed.

Lemma same_tgt : forall t t', same t t' -> same (tgt t) (tgt t').
Proof.
  assert (K : forall t t', (forall c, Interp t c -> exists c', Interp t' c' /\ ceq c c') ->
              forall c, Interp (tgt t) c -> exists c', Interp (tgt t') c' /\ ceq c c').
  { intros t t' H c Hc. inversion Hc; subst.
    destruct (H x H1) as (y & Hy & E).
    exists (ctgt y). split.
    - apply I_tgt; [exact Hy | rewrite <- (cdim_ceq Sg M _ _ E); assumption].
    - apply (ctgt_ceq Sg M); assumption. }
  intros t t' S. pose proof (same_sym _ _ S) as S'. destruct S as [S1 _], S' as [S2 _].
  split; [apply K; exact S1 |].
  intros c Hc. destruct (K t' t S2 c Hc) as (x & Hx & E).
  exists x. split; [exact Hx | apply sy; exact E].
Qed.

Lemma same_id : forall t t', same t t' -> same (id t) (id t').
Proof.
  assert (K : forall t t', (forall c, Interp t c -> exists c', Interp t' c' /\ ceq c c') ->
              forall c, Interp (id t) c -> exists c', Interp (id t') c' /\ ceq c c').
  { intros t t' H c Hc. inversion Hc; subst.
    destruct (H x H1) as (y & Hy & E).
    exists (cid y). split; [apply I_id; exact Hy | apply (cid_ceq Sg M); exact E]. }
  intros t t' S. pose proof (same_sym _ _ S) as S'. destruct S as [S1 _], S' as [S2 _].
  split; [apply K; exact S1 |].
  intros c Hc. destruct (K t' t S2 c Hc) as (x & Hx & E).
  exists x. split; [exact Hx | apply sy; exact E].
Qed.

Lemma same_comp : forall k t t' u u', same t t' -> same u u' ->
  same (comp k t u) (comp k t' u').
Proof.
  assert (K : forall k t t' u u',
              (forall c, Interp t c -> exists c', Interp t' c' /\ ceq c c') ->
              (forall c, Interp u c -> exists c', Interp u' c' /\ ceq c c') ->
              forall c, Interp (comp k t u) c -> exists c', Interp (comp k t' u') c' /\ ceq c c').
  { intros k t t' u u' Ht Hu c Hc. inversion Hc; subst.
    destruct (Ht x H6) as (x' & Hx' & Ex). destruct (Hu y H7) as (y' & Hy' & Ey).
    destruct (composable_ceq Sg M k x y x' y' (conj H1 (conj H2 H3)) Ex Ey) as (P1 & P2 & P3).
    exists (ccomp k x' y' P1 P2 P3). split.
    - apply I_comp; assumption.
    - apply (ccomp_ceq Sg M); assumption. }
  intros k t t' u u' St Su.
  pose proof (same_sym _ _ St) as St'. pose proof (same_sym _ _ Su) as Su'.
  destruct St as [St1 _], Su as [Su1 _], St' as [St2 _], Su' as [Su2 _].
  split; [apply K; assumption |].
  intros c Hc. destruct (K k t' t u' u St2 Su2 c Hc) as (x & Hx & E).
  exists x. split; [exact Hx | apply sy; exact E].
Qed.

Lemma Interp_comp_inv : forall k a b c, Interp (comp k a b) c ->
  exists x y H1 H2 H3, c = ccomp k x y H1 H2 H3 /\ Interp a x /\ Interp b y.
Proof.
  intros k a b c H. inversion H; subst.
  eexists _, _, _, _, _. split; [reflexivity | split; eassumption].
Qed.

(** Inversion of [den] for a composite. *)
Lemma den_comp_inv : forall k a b d, den (comp k a b) d ->
  exists x y H1 H2 H3, Interp a x /\ Interp b y /\ cdim x = d /\
                       Interp (comp k a b) (ccomp k x y H1 H2 H3).
Proof.
  intros k a b d (c & Hc & Hd). inversion Hc; subst.
  exists x, y, H1, H2, H3. repeat split; try assumption.
  rewrite <- (cdim_comp Sg M k x y H1 H2 H3). reflexivity.
Qed.

Theorem soundness :
  (forall x y, x == y -> same x y) /\ (forall t d, wf t d -> den t d).
Proof.
  apply eq_cat_wf_mut.
  - (* E1 *) intros x. split; intros c Hc; exists c; (split; [exact Hc | apply rf]).
  - (* E2 *) intros x y _ IH. apply same_sym. exact IH.
  - (* E3 *) intros x y z _ IH1 _ IH2. apply (same_trans _ y _); assumption.
  - (* E5 *) intros x y n _ IH _ _ _ _. apply same_src. exact IH.
  - (* E6 *) intros x y n _ IH _ _ _ _. apply same_tgt. exact IH.
  - (* E7 *) intros x y z w n d _ IHxy _ IHzw _ _ _ _. apply same_comp; assumption.
  - (* E8 *) intros x y _ IH. apply same_id. exact IH.
  - (* IC1 *) intros x n _ (c & Hc & Hd) Hn.
    apply (same_of_defined _ _ (csrc (csrc c)) (csrc (ctgt c))).
    + apply I_src; [apply I_src; [exact Hc | lia] | rewrite (cdim_src Sg M); lia].
    + apply I_src; [apply I_tgt; [exact Hc | lia] | rewrite (cdim_tgt Sg M); lia].
    + apply (glob_src Sg M). lia.
  - (* IC2 *) intros x n _ (c & Hc & Hd) Hn.
    apply (same_of_defined _ _ (ctgt (csrc c)) (ctgt (ctgt c))).
    + apply I_tgt; [apply I_src; [exact Hc | lia] | rewrite (cdim_src Sg M); lia].
    + apply I_tgt; [apply I_tgt; [exact Hc | lia] | rewrite (cdim_tgt Sg M); lia].
    + apply (glob_tgt Sg M). lia.
  - (* IC3 *) intros x n _ (c & Hc & Hd).
    apply (same_of_defined _ _ (csrc (cid c)) c).
    + apply I_src; [apply I_id; exact Hc | rewrite (cdim_id Sg M); lia].
    + exact Hc.
    + apply (src_id Sg M).
  - (* IC4 *) intros x n _ (c & Hc & Hd).
    apply (same_of_defined _ _ (ctgt (cid c)) c).
    + apply I_tgt; [apply I_id; exact Hc | rewrite (cdim_id Sg M); lia].
    + exact Hc.
    + apply (tgt_id Sg M).
  - (* IC5 *) intros x y n _ IH.
    destruct (den_comp_inv _ _ _ _ IH) as (cy & cx & H1 & H2 & H3 & Hy & Hx & Hd & Hc).
    apply (same_of_defined _ _ (csrc (ccomp n cy cx H1 H2 H3)) (csrc cx)).
    + apply I_src; [exact Hc | rewrite (cdim_comp Sg M); lia].
    + apply I_src; [exact Hx | lia].
    + apply (src_comp_top Sg M). exact Hd.
  - (* IC6 *) intros x y n _ IH.
    destruct (den_comp_inv _ _ _ _ IH) as (cy & cx & H1 & H2 & H3 & Hy & Hx & Hd & Hc).
    apply (same_of_defined _ _ (ctgt (ccomp n cy cx H1 H2 H3)) (ctgt cy)).
    + apply I_tgt; [exact Hc | rewrite (cdim_comp Sg M); lia].
    + apply I_tgt; [exact Hy | lia].
    + apply (tgt_comp_top Sg M). exact Hd.
  - (* IC7 *) intros x y n d _ IH Hdn.
    destruct (den_comp_inv _ _ _ _ IH) as (cy & cx & H1 & H2 & H3 & Hy & Hx & Hd & Hc).
    destruct (composable_src Sg M n cy cx (conj H1 (conj H2 H3)) ltac:(lia)) as (P1 & P2 & P3).
    apply (same_of_defined _ _ (csrc (ccomp n cy cx H1 H2 H3))
                               (ccomp n (csrc cy) (csrc cx) P1 P2 P3)).
    + apply I_src; [exact Hc | rewrite (cdim_comp Sg M); lia].
    + apply I_comp; apply I_src; try assumption; lia.
    + apply (src_comp_low Sg M). lia.
  - (* IC8 *) intros x y n d _ IH Hdn.
    destruct (den_comp_inv _ _ _ _ IH) as (cy & cx & H1 & H2 & H3 & Hy & Hx & Hd & Hc).
    destruct (composable_tgt Sg M n cy cx (conj H1 (conj H2 H3)) ltac:(lia)) as (P1 & P2 & P3).
    apply (same_of_defined _ _ (ctgt (ccomp n cy cx H1 H2 H3))
                               (ccomp n (ctgt cy) (ctgt cx) P1 P2 P3)).
    + apply I_tgt; [exact Hc | rewrite (cdim_comp Sg M); lia].
    + apply I_comp; apply I_tgt; try assumption; lia.
    + apply (tgt_comp_low Sg M). lia.
  - (* IC9 *) intros x y z n d _ (c1 & Hc1 & _) _ (c2 & Hc2 & _).
    apply (same_of_defined _ _ c1 c2 Hc1 Hc2).
    destruct (Interp_comp_inv _ _ _ _ Hc1) as (ab & c & L1 & L2 & L3 & -> & Hab & Hc).
    destruct (Interp_comp_inv _ _ _ _ Hab) as (a & b & A1 & A2 & A3 & -> & Ha & Hb).
    destruct (Interp_comp_inv _ _ _ _ Hc2) as (a' & bc & R1 & R2 & R3 & -> & Ha' & Hbc).
    destruct (Interp_comp_inv _ _ _ _ Hbc) as (b' & c' & B1 & B2 & B3 & -> & Hb' & Hc').
    assert (Ea : ceq a a') by (apply (Interp_fun _ _ Ha _ Ha')).
    assert (Eb : ceq b b') by (apply (Interp_fun _ _ Hb _ Hb')).
    assert (Ec : ceq c c') by (apply (Interp_fun _ _ Hc _ Hc')).
    destruct (composable_ceq Sg M n b' c' b c (conj B1 (conj B2 B3)) (sy _ _ Eb) (sy _ _ Ec))
      as (Q1 & Q2 & Q3).
    assert (Ebc : ceq (ccomp n b' c' B1 B2 B3) (ccomp n b c Q1 Q2 Q3))
      by (apply (ccomp_ceq Sg M); apply sy; assumption).
    destruct (composable_ceq Sg M n a' _ a _ (conj R1 (conj R2 R3)) (sy _ _ Ea) Ebc)
      as (S1 & S2 & S3).
    apply (tr _ (ccomp n a (ccomp n b c Q1 Q2 Q3) S1 S2 S3) _).
    + apply (assoc Sg M).
    + apply (ccomp_ceq Sg M); [exact Ea | apply sy; exact Ebc].
  - (* IC10 *) intros x y z w m n d _ (c1 & Hc1 & _) _ (c2 & Hc2 & _) Hmn.
    apply (same_of_defined _ _ c1 c2 Hc1 Hc2).
    destruct (Interp_comp_inv _ _ _ _ Hc1) as (ab & ce & L1 & L2 & L3 & -> & Hab & Hce).
    destruct (Interp_comp_inv _ _ _ _ Hab) as (a & b & A1 & A2 & A3 & -> & Ha & Hb).
    destruct (Interp_comp_inv _ _ _ _ Hce) as (c & e & B1 & B2 & B3 & -> & Hc & He).
    destruct (Interp_comp_inv _ _ _ _ Hc2) as (ac & be & R1 & R2 & R3 & -> & Hac & Hbe).
    destruct (Interp_comp_inv _ _ _ _ Hac) as (a' & c' & C1 & C2 & C3 & -> & Ha' & Hc').
    destruct (Interp_comp_inv _ _ _ _ Hbe) as (b' & e' & D1 & D2 & D3 & -> & Hb' & He').
    assert (Ea : ceq a a') by (apply (Interp_fun _ _ Ha _ Ha')).
    assert (Eb : ceq b b') by (apply (Interp_fun _ _ Hb _ Hb')).
    assert (Ec : ceq c c') by (apply (Interp_fun _ _ Hc _ Hc')).
    assert (Ee : ceq e e') by (apply (Interp_fun _ _ He _ He')).
    destruct (composable_ceq Sg M m a' c' a c (conj C1 (conj C2 C3)) (sy _ _ Ea) (sy _ _ Ec))
      as (P1 & P2 & P3).
    destruct (composable_ceq Sg M m b' e' b e (conj D1 (conj D2 D3)) (sy _ _ Eb) (sy _ _ Ee))
      as (Q1 & Q2 & Q3).
    assert (E1 : ceq (ccomp m a' c' C1 C2 C3) (ccomp m a c P1 P2 P3))
      by (apply (ccomp_ceq Sg M); apply sy; assumption).
    assert (E2 : ceq (ccomp m b' e' D1 D2 D3) (ccomp m b e Q1 Q2 Q3))
      by (apply (ccomp_ceq Sg M); apply sy; assumption).
    destruct (composable_ceq Sg M n _ _ _ _ (conj R1 (conj R2 R3)) E1 E2) as (S1 & S2 & S3).
    apply (tr _ (ccomp n (ccomp m a c P1 P2 P3) (ccomp m b e Q1 Q2 Q3) S1 S2 S3) _).
    + apply (exchange Sg M). exact Hmn.
    + apply (ccomp_ceq Sg M); apply sy; assumption.
  - (* IC11 *) intros x n d _ (cx & Hx & Hd) Hdn _ IH.
    destruct (den_comp_inv _ _ _ _ IH) as (a & u & H1 & H2 & H3 & Ha & Hu & Hda & Hc).
    apply (same_of_defined _ _ (ccomp n a u H1 H2 H3) a Hc Ha).
    assert (Eu : ceq u (cidext_src (cdim a - n) a)).
    { apply (Interp_fun _ u Hu). unfold cidext_src. rewrite Hda.
      apply Interp_iter_id. apply Interp_iter_src; [exact Ha | lia]. }
    destruct (composable_ceq Sg M n a u a _ (conj H1 (conj H2 H3)) (rf a) Eu) as (P1 & P2 & P3).
    apply (tr _ (ccomp n a (cidext_src (cdim a - n) a) P1 P2 P3) _).
    + apply (ccomp_ceq Sg M); [apply rf | exact Eu].
    + apply (unit_r Sg M).
  - (* IC12 *) intros x n d _ (cx & Hx & Hd) Hdn _ IH.
    destruct (den_comp_inv _ _ _ _ IH) as (u & a & H1 & H2 & H3 & Hu & Ha & Hdu & Hc).
    apply (same_of_defined _ _ (ccomp n u a H1 H2 H3) a Hc Ha).
    assert (Hda : cdim a = d) by lia.
    assert (Eu : ceq u (cidext_tgt (cdim a - n) a)).
    { apply (Interp_fun _ u Hu). unfold cidext_tgt. rewrite Hda.
      apply Interp_iter_id. apply Interp_iter_tgt; [exact Ha | lia]. }
    destruct (composable_ceq Sg M n u a _ a (conj H1 (conj H2 H3)) Eu (rf a)) as (P1 & P2 & P3).
    apply (tr _ (ccomp n (cidext_tgt (cdim a - n) a) a P1 P2 P3) _).
    + apply (ccomp_ceq Sg M); [exact Eu | apply rf].
    + apply (unit_l Sg M).
  - (* IC13 *) intros x y n d _ IH Hdn.
    destruct (den_comp_inv _ _ _ _ IH) as (cy & cx & H1 & H2 & H3 & Hy & Hx & Hd & Hc).
    destruct (composable_id Sg M n cy cx (conj H1 (conj H2 H3))) as (P1 & P2 & P3).
    apply (same_of_defined _ _ (cid (ccomp n cy cx H1 H2 H3))
                               (ccomp n (cid cy) (cid cx) P1 P2 P3)).
    + apply I_id. exact Hc.
    + apply I_comp; apply I_id; assumption.
    + apply (id_comp Sg M).
  - (* wf gen *) intro g. exists (sigma g). split; [apply I_gen | apply Hsig].
  - (* wf src *) intros e n _ (c & Hc & Hd). exists (csrc c). split.
    + apply I_src; [exact Hc | lia].
    + rewrite (cdim_src Sg M); lia.
  - (* wf tgt *) intros e n _ (c & Hc & Hd). exists (ctgt c). split.
    + apply I_tgt; [exact Hc | lia].
    + rewrite (cdim_tgt Sg M); lia.
  - (* wf id *) intros e n _ (c & Hc & Hd). exists (cid c). split.
    + apply I_id; exact Hc.
    + rewrite (cdim_id Sg M); lia.
  - (* wf comp *) intros k a b n _ (ca & Ha & Hda) _ (cb & Hb & Hdb) Hk _ [S1 _].
    assert (C : composable Sg k ca cb).
    { split; [lia | split; [lia |]]. rewrite Hda.
      destruct (S1 _ (Interp_iter_src (n - k) a ca Ha ltac:(lia))) as (c' & Hc' & E).
      apply (tr _ c' _); [exact E |].
      apply (Interp_fun _ c' Hc'). apply Interp_iter_tgt; [exact Hb | lia]. }
    destruct C as (P1 & P2 & P3).
    exists (ccomp k ca cb P1 P2 P3). split.
    + apply I_comp; assumption.
    + rewrite (cdim_comp Sg M). exact Hda.
Qed.

(** Every well-formed term is defined, with a denotation of its dimension. *)
Corollary Interp_total : forall t d, wf t d -> exists c, Interp t c /\ cdim c = d.
Proof. exact (proj2 soundness). Qed.

(** Provably equal terms denote equal cells. *)
Corollary Interp_sound : forall x y c c',
  x == y -> Interp x c -> Interp y c' -> ceq c c'.
Proof.
  intros x y c c' H Hc Hc'.
  destruct (proj1 (proj1 soundness x y H) c Hc) as (z & Hz & E).
  apply (tr _ z _); [exact E | apply (Interp_fun _ _ Hz _ Hc')].
Qed.

(** Provably equal terms are defined together. *)
Corollary defined_eq : forall x y, x == y -> (defined x <-> defined y).
Proof.
  intros x y H. destruct (proj1 soundness x y H) as [A B]. split; intros [c Hc].
  - destruct (A c Hc) as (z & Hz & _). exists z; exact Hz.
  - destruct (B c Hc) as (z & Hz & _). exists z; exact Hz.
Qed.

Lemma wf_defined : forall t d, wf t d -> defined t.
Proof. intros t d H. destruct (Interp_total t d H) as (c & Hc & _). exists c; exact Hc. Qed.

(** ** 3. The map out of the free model *)

Lemma Interp_src_inv : forall e c, Interp (src e) c ->
  exists x, c = csrc x /\ Interp e x /\ cdim x > 0.
Proof. intros e c H. inversion H; subst. eexists. split; [reflexivity | split; eassumption]. Qed.

Lemma Interp_tgt_inv : forall e c, Interp (tgt e) c ->
  exists x, c = ctgt x /\ Interp e x /\ cdim x > 0.
Proof. intros e c H. inversion H; subst. eexists. split; [reflexivity | split; eassumption]. Qed.

Lemma Interp_id_inv : forall e c, Interp (id e) c ->
  exists x, c = cid x /\ Interp e x.
Proof. intros e c H. inversion H; subst. eexists. split; [reflexivity | eassumption]. Qed.

(** The denotation of a defined term, as a function. Recursion is on the
    term; the proof of definedness is only used to build proofs. *)
Fixpoint eval (t : Term) : defined t -> {c : Cell Sg | Interp t c}.
Proof.
  destruct t as [g | e | e | e | k a b]; intro D.
  - exists (sigma g). apply I_gen.
  - assert (De : defined e)
      by (destruct D as [c H]; destruct (Interp_src_inv _ _ H) as (x & _ & Hx & _); exists x; exact Hx).
    destruct (eval e De) as [x Hx].
    exists (csrc x). apply I_src; [exact Hx |].
    destruct D as [c H]. destruct (Interp_src_inv _ _ H) as (x' & _ & Hx' & Hd).
    rewrite (cdim_ceq Sg M _ _ (Interp_fun _ _ Hx _ Hx')). exact Hd.
  - assert (De : defined e)
      by (destruct D as [c H]; destruct (Interp_tgt_inv _ _ H) as (x & _ & Hx & _); exists x; exact Hx).
    destruct (eval e De) as [x Hx].
    exists (ctgt x). apply I_tgt; [exact Hx |].
    destruct D as [c H]. destruct (Interp_tgt_inv _ _ H) as (x' & _ & Hx' & Hd).
    rewrite (cdim_ceq Sg M _ _ (Interp_fun _ _ Hx _ Hx')). exact Hd.
  - assert (De : defined e)
      by (destruct D as [c H]; destruct (Interp_id_inv _ _ H) as (x & _ & Hx); exists x; exact Hx).
    destruct (eval e De) as [x Hx].
    exists (cid x). apply I_id. exact Hx.
  - assert (Da : defined a)
      by (destruct D as [c H]; destruct (Interp_comp_inv _ _ _ _ H) as (x & y & _ & _ & _ & _ & Hx & _);
          exists x; exact Hx).
    assert (Db : defined b)
      by (destruct D as [c H]; destruct (Interp_comp_inv _ _ _ _ H) as (x & y & _ & _ & _ & _ & _ & Hy);
          exists y; exact Hy).
    destruct (eval a Da) as [x Hx]. destruct (eval b Db) as [y Hy].
    assert (C : composable Sg k x y).
    { destruct D as [c H].
      destruct (Interp_comp_inv _ _ _ _ H) as (x' & y' & H1 & H2 & H3 & _ & Hx' & Hy').
      apply (composable_ceq Sg M k x' y' x y (conj H1 (conj H2 H3))).
      - apply (Interp_fun _ _ Hx' _ Hx).
      - apply (Interp_fun _ _ Hy' _ Hy). }
    exists (ccomp k x y (proj1 C) (proj1 (proj2 C)) (proj2 (proj2 C))).
    apply I_comp; assumption.
Defined.

(** The extension of sigma to the free model. *)
Definition ext (c : FreeCell) : Cell Sg :=
  proj1_sig (eval (cell_term c) (wf_defined _ _ (cell_proof c))).

Lemma ext_Interp : forall c : FreeCell, Interp (cell_term c) (ext c).
Proof. intro c. unfold ext. apply proj2_sig. Qed.

Lemma ext_dim : forall c : FreeCell, cdim (ext c) = cell_dim c.
Proof. intro c. apply (Interp_wf_dim (cell_term c)); [apply ext_Interp | exact (cell_proof c)]. Qed.

(** [ext] is an ∞-functor from the free model. *)
Theorem ext_functor : IsFunctor FreeSig Sg ext.
Proof.
  constructor.
  - intros a b H. apply (Interp_sound (cell_term a) (cell_term b));
      [exact H | apply ext_Interp | apply ext_Interp].
  - intro a. apply ext_dim.
  - intros a Hd. apply (Interp_fun (src (cell_term a))).
    + apply I_src; [apply ext_Interp | rewrite ext_dim; exact Hd].
    + pose proof (ext_Interp (Free_src a)) as E.
      rewrite (proj1 (Free_src_proj a Hd)) in E. exact E.
  - intros a Hd. apply (Interp_fun (tgt (cell_term a))).
    + apply I_tgt; [apply ext_Interp | rewrite ext_dim; exact Hd].
    + pose proof (ext_Interp (Free_tgt a)) as E.
      rewrite (proj1 (Free_tgt_proj a Hd)) in E. exact E.
  - intros k a b H1 H2 H3 H1' H2' H3'.
    apply (Interp_fun (comp k (cell_term a) (cell_term b))).
    + exact (ext_Interp (ccomp (o := FreeSig) k a b H1 H2 H3)).
    + apply I_comp; apply ext_Interp.
  - intro a. apply (Interp_fun (id (cell_term a))).
    + exact (ext_Interp (Free_id a)).
    + apply I_id. apply ext_Interp.
Qed.

(** The generators, as cells of the free model. *)
Definition gen_cell (g : Generator) : FreeCell :=
  {| cell_term := gen g; cell_dim := gen_dim g; cell_proof := wf_gen g |}.

(** [ext] extends sigma. *)
Theorem ext_gen : forall g, ceq (ext (gen_cell g)) (sigma g).
Proof. intro g. apply (Interp_fun (gen g)); [apply (ext_Interp (gen_cell g)) | apply I_gen]. Qed.

(** Any functor from the free model that extends sigma sends a cell to the
    denotation of its term. *)
Lemma functor_Interp : forall F : FreeCell -> Cell Sg,
  IsFunctor FreeSig Sg F ->
  (forall g, ceq (F (gen_cell g)) (sigma g)) ->
  forall t x, Interp t x -> forall c : FreeCell, cell_term c = t -> ceq (F c) x.
Proof.
  intros F HF Hgen.
  assert (Same : forall c c' : FreeCell, cell_term c = cell_term c' -> ceq (F c) (F c')).
  { intros c c' E. apply (fun_ceq FreeSig Sg F HF).
    change (cell_term c == cell_term c'). rewrite E. apply E1_refl. }
  induction 1 as [g | e x Hx IH Hd | e x Hx IH Hd | e x Hx IH
                  | k a b x y H1 H2 H3 Hx IHx Hy IHy]; intros [t d p] Hc; simpl in Hc; subst t.
  - apply (tr _ (F (gen_cell g)) _); [apply Same; reflexivity | apply Hgen].
  - assert (pe : wf e (S d)) by (inversion p; subst; assumption).
    set (ce := {| cell_term := e; cell_dim := S d; cell_proof := pe |}).
    apply (tr _ (F (Free_src ce)) _); [apply Same; reflexivity |].
    apply (tr _ (csrc (F ce)) _).
    + apply sy. apply (fun_src FreeSig Sg F HF ce). simpl. lia.
    + apply (csrc_ceq Sg M); [| apply IH; reflexivity].
      rewrite (fun_dim FreeSig Sg F HF). simpl. lia.
  - assert (pe : wf e (S d)) by (inversion p; subst; assumption).
    set (ce := {| cell_term := e; cell_dim := S d; cell_proof := pe |}).
    apply (tr _ (F (Free_tgt ce)) _); [apply Same; reflexivity |].
    apply (tr _ (ctgt (F ce)) _).
    + apply sy. apply (fun_tgt FreeSig Sg F HF ce). simpl. lia.
    + apply (ctgt_ceq Sg M); [| apply IH; reflexivity].
      rewrite (fun_dim FreeSig Sg F HF). simpl. lia.
  - destruct d as [|n]; [inversion p |].
    assert (pe : wf e n) by (inversion p; subst; assumption).
    set (ce := {| cell_term := e; cell_dim := n; cell_proof := pe |}).
    apply (tr _ (F (Free_id ce)) _); [apply Same; reflexivity |].
    apply (tr _ (cid (F ce)) _).
    + apply (fun_id FreeSig Sg F HF ce).
    + apply (cid_ceq Sg M). apply IH. reflexivity.
  - destruct (wf_comp_inv k a b d p) as (pa & pb & Hk & Hbd).
    set (ca := {| cell_term := a; cell_dim := d; cell_proof := pa |}).
    set (cb := {| cell_term := b; cell_dim := d; cell_proof := pb |}).
    assert (Hf3 : FreeCell_eq (Nat.iter (cell_dim ca - k) Free_src ca)
                              (Nat.iter (cell_dim ca - k) Free_tgt cb)).
    { unfold FreeCell_eq.
      rewrite (proj1 (Free_iter_src_proj (cell_dim ca - k) ca ltac:(simpl; lia))).
      rewrite (proj1 (Free_iter_tgt_proj (cell_dim ca - k) cb ltac:(simpl; lia))).
      exact Hbd. }
    set (cc := ccomp (o := FreeSig) k ca cb eq_refl Hk Hf3).
    destruct (fun_composable FreeSig Sg FreeModel_is_EqCat_model M F HF k ca cb eq_refl Hk Hf3)
      as (P1 & P2 & P3).
    apply (tr _ (F cc) _); [apply Same; reflexivity |].
    apply (tr _ (ccomp k (F ca) (F cb) P1 P2 P3) _).
    + apply (fun_comp FreeSig Sg F HF).
    + apply (ccomp_ceq Sg M); [apply IHx | apply IHy]; reflexivity.
Qed.

(** [ext] is the only functor from the free model that extends sigma. *)
Theorem ext_unique : forall F : FreeCell -> Cell Sg,
  IsFunctor FreeSig Sg F ->
  (forall g, ceq (F (gen_cell g)) (sigma g)) ->
  forall c : FreeCell, ceq (F c) (ext c).
Proof.
  intros F HF Hgen c.
  apply (functor_Interp F HF Hgen (cell_term c) (ext c) (ext_Interp c) c eq_refl).
Qed.

End Interpretation.

(** The universal property of the free model, in one statement: for every
    model and every dimension-preserving assignment of its cells to the
    generators there is a functor from the free model extending the
    assignment, and any two such functors agree. *)
Theorem free_model_universal :
  forall (Sg : OmegaSig), IsEqCatModel Sg ->
  forall sigma : Generator -> Cell Sg,
  (forall g, cdim (sigma g) = gen_dim g) ->
  exists F : FreeCell -> Cell Sg,
    IsFunctor FreeSig Sg F /\
    (forall g, ceq (F (gen_cell g)) (sigma g)) /\
    (forall F' : FreeCell -> Cell Sg,
       IsFunctor FreeSig Sg F' ->
       (forall g, ceq (F' (gen_cell g)) (sigma g)) ->
       forall c, ceq (F' c) (F c)).
Proof.
  intros Sg M sigma Hsig. exists (ext Sg M sigma Hsig). split; [| split].
  - apply ext_functor.
  - apply ext_gen.
  - apply ext_unique.
Qed.

(** The free model is a strict ω-category. *)
Corollary free_model_strict : IsStrictOmegaCat FreeSig.
Proof. apply model_is_strict. apply FreeModel_is_EqCat_model. Qed.

End UniversalF.

(** Assumption check on a concrete set of generators. *)
Module UnivGen <: GEN.
  Inductive G := x | f.
  Definition Generator := G.
  Definition gen_dim (g : G) : nat := match g with x => 0 | f => 1 end.
  Definition Generator_eq_dec : forall g1 g2 : Generator, {g1 = g2} + {g1 <> g2}.
  Proof. decide equality. Defined.
End UnivGen.
Module Univ := UniversalF UnivGen.
Print Assumptions Univ.soundness.
Print Assumptions Univ.free_model_universal.
Print Assumptions Univ.free_model_strict.
