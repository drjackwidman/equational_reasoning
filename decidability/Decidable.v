(** * Decidable.v
    Decidability of provable equality in the strict free model (Theorem 4.6).

    Architecture (see header discussion in the development):
      - [normalize_sound]    : normalize is sound w.r.t. ==          [ADMITTED]
      - [toTerm_inj]         : Lemma 4.2 — canonical normal forms are
                               not == unless equal (the deep lemma;
                               confluence / semantic core)            [ADMITTED]
      - [normalize_total]    : normalize succeeds on wf terms (uses injectivity
                               in the comp case)
      - [normalize_complete] : == implies equal normal forms (from the above)
      - [free_cell_decidable]: Theorem 4.6 (from completeness + soundness + totality)

    PROOF STATUS. This file is NOT yet admit-free. Five lemmas below are
    [Admitted] and carry the irreducible combinatorial / confluence content
    of §4:
      [toTerm_inj], [nf_comp_glue], [normalize_sound],
      [src_pow_sound], [tgt_pow_sound].
    Everything else here — including [normalize_total], [normalize_complete],
    and [free_cell_decidable] — is proved [Qed], but those proofs are built
    FROM the five admitted lemmas and therefore inherit them as assumptions.
    So decidability is established only *modulo* those five lemmas;
    [Print Assumptions free_cell_decidable] lists exactly them. *)

Require Import Arith PeanoNat Lia Bool.
Require Import Syntax Axioms Meta NormalForm FreeModel.

(* Set Implicit Arguments. *)

(** ** Iteration / arithmetic helpers *)

Lemma iter_id_add : forall a b X, iter_id (a + b) X = iter_id a (iter_id b X).
Proof. induction a; intros; simpl; [reflexivity | rewrite IHa; reflexivity]. Qed.

Lemma iter_src_add : forall a b X, iter_src (a + b) X = iter_src a (iter_src b X).
Proof. induction a; intros; simpl; [reflexivity | rewrite IHa; reflexivity]. Qed.

Lemma iter_tgt_add : forall a b X, iter_tgt (a + b) X = iter_tgt a (iter_tgt b X).
Proof. induction a; intros; simpl; [reflexivity | rewrite IHa; reflexivity]. Qed.

(** ** Canonical-form preservation by the unary smart constructors *)

Lemma nf_src_canonical : forall u w, canonical u -> nf_src u = Some w -> canonical w.
Proof.
  intros u w Hc Hs. unfold nf_src in Hs. destruct (nl u) eqn:E.
  - destruct (nm u <? gen_dim (na u)) eqn:Eb; [|discriminate].
    injection Hs; intro Hw; subst w.
    unfold canonical; cbn [nm ne]. intro H0; discriminate H0.
  - injection Hs; intro Hw; subst w.
    unfold canonical in *; cbn [nm ne] in *. exact Hc.
Qed.

Lemma nf_tgt_canonical : forall u w, canonical u -> nf_tgt u = Some w -> canonical w.
Proof.
  intros u w Hc Hs. unfold nf_tgt in Hs. destruct (nl u) eqn:E.
  - destruct (nm u <? gen_dim (na u)) eqn:Eb; [|discriminate].
    injection Hs; intro Hw; subst w.
    unfold canonical; cbn [nm ne]. intro H0; discriminate H0.
  - injection Hs; intro Hw; subst w.
    unfold canonical in *; cbn [nm ne] in *. exact Hc.
Qed.

(** ** Commutation lemmas relating normalize-level [src_pow]/[tgt_pow]/[idext]
       to the term-level iterated operators. NF-only, no circularity. *)

(** toTerm of an iterated-src normal form is provably the iterated src of toTerm.
    [ADMITTED] — one of the five remaining lemmas (see file header). *)
Lemma src_pow_sound : forall c u,
  nwf u -> c <= ndim u -> toTerm (src_pow c u) == iter_src c (toTerm u).
Proof. Admitted.

(** Symmetric to [src_pow_sound].
    [ADMITTED] — one of the five remaining lemmas (see file header). *)
Lemma tgt_pow_sound : forall c u,
  nwf u -> c <= ndim u -> toTerm (tgt_pow c u) == iter_tgt c (toTerm u).
Proof. Admitted.

(** idext is id^c of the corresponding pow — pure arithmetic on toTerm. *)
Lemma toTerm_idext_src : forall c u,
  toTerm (idext_src c u) = iter_id c (toTerm (src_pow c u)).
Proof.
  intros c u. unfold idext_src, toTerm. cbn [nl ne nm na].
  rewrite (Nat.add_comm (nl (src_pow c u)) c). rewrite iter_id_add. reflexivity.
Qed.

Lemma toTerm_idext_tgt : forall c u,
  toTerm (idext_tgt c u) = iter_id c (toTerm (tgt_pow c u)).
Proof.
  intros c u. unfold idext_tgt, toTerm. cbn [nl ne nm na].
  rewrite (Nat.add_comm (nl (tgt_pow c u)) c). rewrite iter_id_add. reflexivity.
Qed.

(** ** Well-formedness / canonicity of [src_pow]/[tgt_pow]. *)

Lemma src_pow_nwf : forall c u, nwf u -> c <= ndim u -> nwf (src_pow c u).
Proof.
  intros c u Hn Hd. unfold src_pow. destruct (c <=? nl u) eqn:E.
  - unfold nwf in *; cbn [nm na]. exact Hn.
  - apply Nat.leb_gt in E. unfold nwf, ndim in *; cbn [nm na]. lia.
Qed.

Lemma tgt_pow_nwf : forall c u, nwf u -> c <= ndim u -> nwf (tgt_pow c u).
Proof.
  intros c u Hn Hd. unfold tgt_pow. destruct (c <=? nl u) eqn:E.
  - unfold nwf in *; cbn [nm na]. exact Hn.
  - apply Nat.leb_gt in E. unfold nwf, ndim in *; cbn [nm na]. lia.
Qed.

Lemma src_pow_canonical : forall c u, canonical u -> canonical (src_pow c u).
Proof.
  intros c u Hc. unfold src_pow. destruct (c <=? nl u) eqn:E.
  - unfold canonical in *; cbn [nm ne]. exact Hc.
  - unfold canonical; cbn [ne]. intros _; reflexivity.
Qed.

Lemma tgt_pow_canonical : forall c u, canonical u -> canonical (tgt_pow c u).
Proof.
  intros c u Hc. unfold tgt_pow. destruct (c <=? nl u) eqn:E.
  - unfold canonical in *; cbn [nm ne]. exact Hc.
  - apply Nat.leb_gt in E. unfold canonical; cbn [nm ne]. intro H0; lia.
Qed.

(** ** Iterated src/tgt preserve well-formedness and are congruences. *)

Lemma wf_iter_src : forall c x d, wf x d -> c <= d -> wf (iter_src c x) (d - c).
Proof.
  induction c; intros x d Hx Hc.
  - rewrite Nat.sub_0_r. exact Hx.
  - change (iter_src (S c) x) with (src (iter_src c x)).
    apply (wf_src (iter_src c x) (d - S c)).
    replace (S (d - S c)) with (d - c) by lia.
    apply IHc; [exact Hx | lia].
Qed.

Lemma wf_iter_tgt : forall c x d, wf x d -> c <= d -> wf (iter_tgt c x) (d - c).
Proof.
  induction c; intros x d Hx Hc.
  - rewrite Nat.sub_0_r. exact Hx.
  - change (iter_tgt (S c) x) with (tgt (iter_tgt c x)).
    apply (wf_tgt (iter_tgt c x) (d - S c)).
    replace (S (d - S c)) with (d - c) by lia.
    apply IHc; [exact Hx | lia].
Qed.

Lemma iter_src_cong : forall c x y d,
  x == y -> wf x d -> wf y d -> c <= d -> iter_src c x == iter_src c y.
Proof.
  induction c; intros x y d Hxy Hx Hy Hc.
  - exact Hxy.
  - change (iter_src (S c) x) with (src (iter_src c x)).
    change (iter_src (S c) y) with (src (iter_src c y)).
    apply (E5_src (iter_src c x) (iter_src c y) (d - S c)).
    + apply (IHc x y d); [exact Hxy | exact Hx | exact Hy | lia].
    + replace (S (d - S c)) with (d - c) by lia. apply wf_iter_src; [exact Hx | lia].
    + replace (S (d - S c)) with (d - c) by lia. apply wf_iter_src; [exact Hy | lia].
Qed.

Lemma iter_tgt_cong : forall c x y d,
  x == y -> wf x d -> wf y d -> c <= d -> iter_tgt c x == iter_tgt c y.
Proof.
  induction c; intros x y d Hxy Hx Hy Hc.
  - exact Hxy.
  - change (iter_tgt (S c) x) with (tgt (iter_tgt c x)).
    change (iter_tgt (S c) y) with (tgt (iter_tgt c y)).
    apply (E6_tgt (iter_tgt c x) (iter_tgt c y) (d - S c)).
    + apply (IHc x y d); [exact Hxy | exact Hx | exact Hy | lia].
    + replace (S (d - S c)) with (d - c) by lia. apply wf_iter_tgt; [exact Hx | lia].
    + replace (S (d - S c)) with (d - c) by lia. apply wf_iter_tgt; [exact Hy | lia].
Qed.

(** ** Soundness of the normalizer (independent of injectivity).
    [ADMITTED] — one of the five remaining lemmas (see file header). *)
Theorem normalize_sound : forall t d u,
  wf t d -> normalize t = Some u -> toTerm u == t.
Proof. Admitted.
Arguments normalize_sound {t d u}.

(** ** Lemma 4.2 (injectivity of the normal-form interpretation).
    THE deep lemma: distinct canonical, well-formed normal forms denote
    distinct cells of the free model. Equivalent to confluence of §4.
    [ADMITTED] — one of the five remaining lemmas (see file header). *)
Theorem toTerm_inj : forall u v,
  nwf u -> canonical u -> nwf v -> canonical v ->
  toTerm u == toTerm v -> u = v.
Proof. Admitted.

(** ** Lemma 4.4 combinatorial step: from a matched boundary (as NF equality)
    the composite is degenerate and [nf_comp] succeeds with a well-formed,
    canonical result that denotes the composite.
    [ADMITTED] — one of the five remaining lemmas (see file header). *)
Lemma nf_comp_glue : forall k a b n u v,
  wf a n -> wf b n -> k < n ->
  normalize a = Some u -> normalize b = Some v ->
  nwf u -> canonical u -> ndim u = n ->
  nwf v -> canonical v -> ndim v = n ->
  src_pow (n - k) u = tgt_pow (n - k) v ->
  exists w, nf_comp k u v = Some w /\ nwf w /\ canonical w /\ ndim w = n
            /\ toTerm w == comp k a b.
Proof. Admitted.

(** ** Totality of the normalizer on well-formed terms. *)
Theorem normalize_total : forall t d,
  wf t d ->
  exists u, normalize t = Some u /\ nwf u /\ canonical u /\ ndim u = d.
Proof.
  intros t d H. induction H.
  - (* gen *)
    exists (mkNF 0 Es 0 g).
    split; [reflexivity|].
    split; [unfold nwf; cbn; lia|].
    split; [unfold canonical; cbn; reflexivity|].
    unfold ndim; cbn; lia.
  - (* src e, wf e (S n) *)
    destruct IHwf as (u & Hu & Hnu & Hcu & Hdu).
    assert (Hd : ndim u > 0) by lia.
    destruct (nf_src_spec Hnu Hd) as (w & Hsw & Hnw & Hdw & Htw).
    exists w. rewrite normalize_src_eq, Hu, Hsw.
    split; [reflexivity|].
    split; [exact Hnw|].
    split; [apply (nf_src_canonical _ _ Hcu Hsw)|].
    lia.
  - (* tgt e *)
    destruct IHwf as (u & Hu & Hnu & Hcu & Hdu).
    assert (Hd : ndim u > 0) by lia.
    destruct (nf_tgt_spec Hnu Hd) as (w & Hsw & Hnw & Hdw & Htw).
    exists w. rewrite normalize_tgt_eq, Hu, Hsw.
    split; [reflexivity|].
    split; [exact Hnw|].
    split; [apply (nf_tgt_canonical _ _ Hcu Hsw)|].
    lia.
  - (* id e *)
    destruct IHwf as (u & Hu & Hnu & Hcu & Hdu).
    destruct (nf_id_spec Hnu) as (Hnw & Hdw & Htw).
    exists (nf_id u). rewrite normalize_id_eq, Hu.
    split; [reflexivity|].
    split; [exact Hnw|].
    split; [unfold canonical, nf_id; cbn [nl ne nm na]; exact Hcu|].
    lia.
  - (* comp k a b *)
    destruct IHwf1 as (u & Hu & Hnu & Hcu & Hdu).
    destruct IHwf2 as (v & Hv & Hnv & Hcv & Hdv).
    (* soundness of the operands' normal forms *)
    assert (Hsu : toTerm u == a) by exact (normalize_sound H Hu).
    assert (Hsv : toTerm v == b) by exact (normalize_sound H0 Hv).
    assert (Hwu : wf (toTerm u) n) by (rewrite <- Hdu; apply toTerm_wf; exact Hnu).
    assert (Hwv : wf (toTerm v) n) by (rewrite <- Hdv; apply toTerm_wf; exact Hnv).
    (* boundary, via soundness + injectivity, yields src_pow = tgt_pow *)
    assert (Hglue : src_pow (n - k) u = tgt_pow (n - k) v).
    { apply toTerm_inj.
      - apply src_pow_nwf; [exact Hnu | lia].
      - apply src_pow_canonical; exact Hcu.
      - apply tgt_pow_nwf; [exact Hnv | lia].
      - apply tgt_pow_canonical; exact Hcv.
      - (* toTerm (src_pow c u) == toTerm (tgt_pow c v) *)
        apply (E3_trans (toTerm (src_pow (n - k) u))
                        (iter_src (n - k) a)
                        (toTerm (tgt_pow (n - k) v))).
        + apply (E3_trans (toTerm (src_pow (n - k) u))
                          (iter_src (n - k) (toTerm u))
                          (iter_src (n - k) a)).
          * apply src_pow_sound; [exact Hnu | lia].
          * apply (iter_src_cong (n - k) (toTerm u) a n);
              [exact Hsu | exact Hwu | exact H | lia].
        + apply (E3_trans (iter_src (n - k) a)
                          (iter_tgt (n - k) b)
                          (toTerm (tgt_pow (n - k) v))).
          * exact H2. (* the boundary premise *)
          * apply (E3_trans (iter_tgt (n - k) b)
                            (iter_tgt (n - k) (toTerm v))
                            (toTerm (tgt_pow (n - k) v))).
            -- apply (iter_tgt_cong (n - k) b (toTerm v) n);
                 [apply E2_sym; exact Hsv | exact H0 | exact Hwv | lia].
            -- apply E2_sym; apply tgt_pow_sound; [exact Hnv | lia]. }
    destruct (nf_comp_glue _ _ _ _ _ _ H H0 H1 Hu Hv Hnu Hcu Hdu Hnv Hcv Hdv Hglue)
      as (w & Hcw & Hnw & Hcanw & Hdw & Htw).
    exists w. rewrite normalize_comp_eq, Hu, Hv. rewrite Hcw.
    split; [reflexivity|].
    split; [exact Hnw|].
    split; [exact Hcanw|].
    exact Hdw.
Qed.

Arguments normalize_total {t d}.

(** ** Completeness: provable equality implies identical normal forms. *)
Theorem normalize_complete : forall t1 t2 d1 d2,
  wf t1 d1 -> wf t2 d2 -> t1 == t2 -> normalize t1 = normalize t2.
Proof.
  intros t1 t2 d1 d2 H1 H2 Heq.
  destruct (normalize_total H1) as (u & Hu & Hnu & Hcu & Hdu).
  destruct (normalize_total H2) as (v & Hv & Hnv & Hcv & Hdv).
  rewrite Hu, Hv. f_equal.
  apply toTerm_inj; try assumption.
  apply (E3_trans (toTerm u) t1 (toTerm v)).
  - apply (normalize_sound H1 Hu).
  - apply (E3_trans t1 t2 (toTerm v)).
    + exact Heq.
    + apply E2_sym. apply (normalize_sound H2 Hv).
Qed.

Arguments normalize_complete {t1 t2 d1 d2}.

(** ** Theorem 4.6: decidability of equality in the strict free model. *)
Theorem free_cell_decidable : forall c1 c2 : FreeCell, {c1 === c2} + {~ c1 === c2}.
Proof.
  intros [t1 d1 p1] [t2 d2 p2]. unfold FreeCell_eq; simpl.
  (* Compute normal forms directly; totality rules out the None branches. *)
  destruct (normalize t1) as [u|] eqn:Hu.
  2:{ exfalso. destruct (normalize_total p1) as (u & Hu' & _).
      rewrite Hu in Hu'; discriminate. }
  destruct (normalize t2) as [v|] eqn:Hv.
  2:{ exfalso. destruct (normalize_total p2) as (v & Hv' & _).
      rewrite Hv in Hv'; discriminate. }
  destruct (NF_eq_dec u v) as [E | N].
  - left.
    apply (E3_trans t1 (toTerm u) t2).
    + apply E2_sym; apply (normalize_sound p1 Hu).
    + subst v. apply (normalize_sound p2 Hv).
  - right. intro Hc. apply N.
    assert (Hnn : normalize t1 = normalize t2)
      by (apply (normalize_complete p1 p2 Hc)).
    rewrite Hu, Hv in Hnn. injection Hnn; auto.
Qed.
