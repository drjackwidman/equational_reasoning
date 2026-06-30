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

    PROOF STATUS. This file is admit-free. [toTerm_inj] is discharged by
    [Model.toTerm_inj] (proved in [Model.v] via the combined [eq_cat]/[wf]
    mutual induction [Model.interp_sound_mut]); [normalize_sound] is a
    corollary of the strengthened [normalize_total]; and [src_pow_sound],
    [tgt_pow_sound], [nf_comp_glue] are proved below. Hence
    [Print Assumptions free_cell_decidable] lists only the three intended
    abstract generator parameters ([Generator], [gen_dim], [Generator_eq_dec]). *)

Require Import Arith PeanoNat Lia Bool.
Require Import Syntax Axioms Meta NormalForm FreeModel Model.

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

(** [src_pow_sound] and [tgt_pow_sound] are now PROVED (no longer admitted).
    Their proofs appear further below, after the [iter_src_cong] /
    [iter_tgt_cong] congruence lemmas that they depend on. *)

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

(** ** Commutation lemmas: NF-level [src_pow]/[tgt_pow] match the term-level
       iterated [src]/[tgt]. These are [src_pow_sound] / [tgt_pow_sound], two
       of the formerly-admitted lemmas, now proved. NF-only, no circularity:
       they use only the structural axioms (IC1–IC4) and the congruence /
       well-formedness lemmas above. *)

(** Peel one application from the INSIDE of an iteration (the stdlib only
    provides the outside peel [Nat.iter_succ]). *)
Lemma iter_inside : forall (f : Term -> Term) c t,
  Nat.iter (S c) f t = Nat.iter c f (f t).
Proof.
  intros f. induction c as [|c' IH]; intro t;
    [reflexivity | simpl; rewrite <- IH; reflexivity].
Qed.

(** Cancellation: [c] sources strip [c] identities pairwise (each pair killed by
    IC3, [src (id x) == x]). No dimension bound needed. *)
Lemma iter_src_id_cancel : forall c Y d, wf Y d -> iter_src c (iter_id c Y) == Y.
Proof.
  induction c as [|c' IH]; intros Y d HY.
  - simpl. apply E1_refl.
  - rewrite (iter_id_S c' Y).
    unfold iter_src. rewrite (iter_inside src c' (id (iter_id c' Y))).
    set (W := iter_id c' Y).
    assert (HW : wf W (d + c')) by (apply (wf_iter_id c' HY)).
    apply (E3_trans (Nat.iter c' src (src (id W))) (Nat.iter c' src W) Y).
    + apply (iter_src_cong c' (src (id W)) W (d + c')).
      * apply (IC3 W (d + c') HW).
      * apply (wf_src (id W) (d + c')). apply (wf_id W (d + c') HW).
      * exact HW.
      * lia.
    + unfold W. exact (IH Y d HY).
Qed.

(** Build a src-block: [S j] sources land on an end-block as a single [Es]-block
    (iterating [src_end_collapse], driven by IC1/IC2). *)
Lemma iter_src_end_build : forall j m e a,
  S m + j <= gen_dim a ->
  iter_src (S j) (iter_end e m (gen a)) == iter_end Es (S m + j) (gen a).
Proof.
  induction j as [|j' IH]; intros m e a Hb.
  - unfold iter_src; simpl. rewrite Nat.add_0_r. apply (src_end_collapse e). lia.
  - unfold iter_src. rewrite (iter_inside src (S j') (iter_end e m (gen a))).
    apply (E3_trans (Nat.iter (S j') src (src (iter_end e m (gen a))))
                    (Nat.iter (S j') src (iter_end Es (S m) (gen a)))
                    (iter_end Es (S m + S j') (gen a))).
    + apply (iter_src_cong (S j') (src (iter_end e m (gen a)))
                           (iter_end Es (S m) (gen a)) (gen_dim a - S m)).
      * apply (src_end_collapse e). lia.
      * apply (wf_src (iter_end e m (gen a)) (gen_dim a - S m)).
        replace (S (gen_dim a - S m)) with (gen_dim a - m) by lia.
        apply (wf_iter_end e). lia.
      * apply (wf_iter_end Es). lia.
      * lia.
    + change (Nat.iter (S j') src (iter_end Es (S m) (gen a)))
        with (iter_src (S j') (iter_end Es (S m) (gen a))).
      replace (S m + S j') with (S (S m) + j') by lia. apply IH. lia.
Qed.

(** [src_pow_sound]: the NF-level iterated source is faithful to the term-level
    one. Case split mirrors [src_pow]: enough identities to strip (cancellation)
    vs. not (cancel all ids, then build a src-block). *)
Lemma src_pow_sound : forall c u,
  nwf u -> c <= ndim u -> toTerm (src_pow c u) == iter_src c (toTerm u).
Proof.
  intros c [l e m a] Hnwf Hdim.
  unfold nwf in Hnwf; cbn [na nm] in Hnwf.
  unfold ndim in Hdim; cbn [nl na nm] in Hdim.
  set (B := iter_end e m (gen a)).
  assert (HB : wf B (gen_dim a - m)) by (unfold B; apply (wf_iter_end e); exact Hnwf).
  unfold src_pow; cbn [nl ne nm na].
  destruct (le_gt_dec c l) as [Hle | Hgt].
  - assert (E : (c <=? l) = true) by (apply Nat.leb_le; exact Hle).
    rewrite E. unfold toTerm; cbn [nl ne nm na]. fold B.
    apply E2_sym.
    replace (iter_id l B) with (iter_id c (iter_id (l - c) B))
      by (rewrite <- iter_id_add; f_equal; lia).
    apply (iter_src_id_cancel c (iter_id (l - c) B) ((gen_dim a - m) + (l - c))).
    apply (wf_iter_id (l - c) HB).
  - assert (E : (c <=? l) = false) by (apply Nat.leb_gt; exact Hgt).
    rewrite E. unfold toTerm; cbn [nl ne nm na iter_id]. fold B.
    assert (Hsplit : iter_src c (iter_id l B)
                     = iter_src (c - l) (iter_src l (iter_id l B)))
      by (rewrite <- iter_src_add; f_equal; lia).
    assert (Hmain : iter_src c (iter_id l B) == iter_end Es (m + (c - l)) (gen a)).
    { rewrite Hsplit.
      apply (E3_trans (iter_src (c - l) (iter_src l (iter_id l B)))
                      (iter_src (c - l) B)
                      (iter_end Es (m + (c - l)) (gen a))).
      - apply (iter_src_cong (c - l) (iter_src l (iter_id l B)) B (gen_dim a - m)).
        + apply (iter_src_id_cancel l B (gen_dim a - m) HB).
        + replace (gen_dim a - m) with (((gen_dim a - m) + l) - l) by lia.
          apply (wf_iter_src l (iter_id l B) ((gen_dim a - m) + l));
            [apply (wf_iter_id l HB) | lia].
        + exact HB.
        + lia.
      - destruct (c - l) as [|j'] eqn:Hcl; [lia|].
        unfold B. replace (m + S j') with (S m + j') by lia.
        apply (iter_src_end_build j' m e a). lia. }
    exact (E2_sym _ _ Hmain).
Qed.

(** Mirror of [iter_src_id_cancel] (uses IC4 instead of IC3). *)
Lemma iter_tgt_id_cancel : forall c Y d, wf Y d -> iter_tgt c (iter_id c Y) == Y.
Proof.
  induction c as [|c' IH]; intros Y d HY.
  - simpl. apply E1_refl.
  - rewrite (iter_id_S c' Y).
    unfold iter_tgt. rewrite (iter_inside tgt c' (id (iter_id c' Y))).
    set (W := iter_id c' Y).
    assert (HW : wf W (d + c')) by (apply (wf_iter_id c' HY)).
    apply (E3_trans (Nat.iter c' tgt (tgt (id W))) (Nat.iter c' tgt W) Y).
    + apply (iter_tgt_cong c' (tgt (id W)) W (d + c')).
      * apply (IC4 W (d + c') HW).
      * apply (wf_tgt (id W) (d + c')). apply (wf_id W (d + c') HW).
      * exact HW.
      * lia.
    + unfold W. exact (IH Y d HY).
Qed.

(** Mirror of [iter_src_end_build] (uses [tgt_end_collapse]). *)
Lemma iter_tgt_end_build : forall j m e a,
  S m + j <= gen_dim a ->
  iter_tgt (S j) (iter_end e m (gen a)) == iter_end Et (S m + j) (gen a).
Proof.
  induction j as [|j' IH]; intros m e a Hb.
  - unfold iter_tgt; simpl. rewrite Nat.add_0_r. apply (tgt_end_collapse e). lia.
  - unfold iter_tgt. rewrite (iter_inside tgt (S j') (iter_end e m (gen a))).
    apply (E3_trans (Nat.iter (S j') tgt (tgt (iter_end e m (gen a))))
                    (Nat.iter (S j') tgt (iter_end Et (S m) (gen a)))
                    (iter_end Et (S m + S j') (gen a))).
    + apply (iter_tgt_cong (S j') (tgt (iter_end e m (gen a)))
                           (iter_end Et (S m) (gen a)) (gen_dim a - S m)).
      * apply (tgt_end_collapse e). lia.
      * apply (wf_tgt (iter_end e m (gen a)) (gen_dim a - S m)).
        replace (S (gen_dim a - S m)) with (gen_dim a - m) by lia.
        apply (wf_iter_end e). lia.
      * apply (wf_iter_end Et). lia.
      * lia.
    + change (Nat.iter (S j') tgt (iter_end Et (S m) (gen a)))
        with (iter_tgt (S j') (iter_end Et (S m) (gen a))).
      replace (S m + S j') with (S (S m) + j') by lia. apply IH. lia.
Qed.

(** [tgt_pow_sound]: mirror of [src_pow_sound]. *)
Lemma tgt_pow_sound : forall c u,
  nwf u -> c <= ndim u -> toTerm (tgt_pow c u) == iter_tgt c (toTerm u).
Proof.
  intros c [l e m a] Hnwf Hdim.
  unfold nwf in Hnwf; cbn [na nm] in Hnwf.
  unfold ndim in Hdim; cbn [nl na nm] in Hdim.
  set (B := iter_end e m (gen a)).
  assert (HB : wf B (gen_dim a - m)) by (unfold B; apply (wf_iter_end e); exact Hnwf).
  unfold tgt_pow; cbn [nl ne nm na].
  destruct (le_gt_dec c l) as [Hle | Hgt].
  - assert (E : (c <=? l) = true) by (apply Nat.leb_le; exact Hle).
    rewrite E. unfold toTerm; cbn [nl ne nm na]. fold B.
    apply E2_sym.
    replace (iter_id l B) with (iter_id c (iter_id (l - c) B))
      by (rewrite <- iter_id_add; f_equal; lia).
    apply (iter_tgt_id_cancel c (iter_id (l - c) B) ((gen_dim a - m) + (l - c))).
    apply (wf_iter_id (l - c) HB).
  - assert (E : (c <=? l) = false) by (apply Nat.leb_gt; exact Hgt).
    rewrite E. unfold toTerm; cbn [nl ne nm na iter_id]. fold B.
    assert (Hsplit : iter_tgt c (iter_id l B)
                     = iter_tgt (c - l) (iter_tgt l (iter_id l B)))
      by (rewrite <- iter_tgt_add; f_equal; lia).
    assert (Hmain : iter_tgt c (iter_id l B) == iter_end Et (m + (c - l)) (gen a)).
    { rewrite Hsplit.
      apply (E3_trans (iter_tgt (c - l) (iter_tgt l (iter_id l B)))
                      (iter_tgt (c - l) B)
                      (iter_end Et (m + (c - l)) (gen a))).
      - apply (iter_tgt_cong (c - l) (iter_tgt l (iter_id l B)) B (gen_dim a - m)).
        + apply (iter_tgt_id_cancel l B (gen_dim a - m) HB).
        + replace (gen_dim a - m) with (((gen_dim a - m) + l) - l) by lia.
          apply (wf_iter_tgt l (iter_id l B) ((gen_dim a - m) + l));
            [apply (wf_iter_id l HB) | lia].
        + exact HB.
        + lia.
      - destruct (c - l) as [|j'] eqn:Hcl; [lia|].
        unfold B. replace (m + S j') with (S m + j') by lia.
        apply (iter_tgt_end_build j' m e a). lia. }
    exact (E2_sym _ _ Hmain).
Qed.

(** ** Soundness of the normalizer (independent of injectivity).
    NOW PROVED as a corollary of the strengthened [normalize_total] below
    (which carries the soundness conjunct [toTerm u == t]); the definition
    appears immediately after [normalize_total]. *)

(** ** Lemma 4.2 (injectivity of the normal-form interpretation).
    THE deep lemma: distinct canonical, well-formed normal forms denote
    distinct cells of the free model. Discharged by the total semantic
    interpretation of [Model.v] ([Model.toTerm_inj], proved by the combined
    [eq_cat]/[wf] mutual induction in [Model.interp_sound_mut]). *)
Theorem toTerm_inj : forall u v,
  nwf u -> canonical u -> nwf v -> canonical v ->
  toTerm u == toTerm v -> u = v.
Proof. exact Model.toTerm_inj. Qed.

(** Iterated [id] is a congruence (E8_id carries no [wf] premise). *)
Lemma iter_id_cong : forall c x y, x == y -> iter_id c x == iter_id c y.
Proof.
  induction c as [|c' IH]; intros x y H.
  - exact H.
  - rewrite !iter_id_S. apply E8_id. apply IH. exact H.
Qed.

(** ** Lemma 4.4 combinatorial step: from a matched boundary (as NF equality)
    the composite is degenerate and [nf_comp] succeeds with a well-formed,
    canonical result that denotes the composite.

    NOW PROVED (no longer admitted). Two extra hypotheses [toTerm u == a] and
    [toTerm v == b] are taken as inputs: these are exactly the inductive
    hypotheses available at the sole call site ([normalize_total]), and taking
    them here keeps this lemma INDEPENDENT of [normalize_sound] (whose own
    [comp] case is what calls this lemma — so making it depend on
    [normalize_sound] would be circular).

    The matched boundary forces, via [m_comp_boundary], one of two unit
    patterns: either [v] is the right identity-extension of [u] (so the
    composite collapses to [a] by IC11), or [u] is the left identity-extension
    of [v] (collapse to [b] by IC12). In each case [nf_comp] returns the
    surviving operand and [E7_comp] + the unit law identify it with
    [comp k a b]. *)
Lemma nf_comp_glue : forall k a b n u v,
  wf a n -> wf b n -> k < n ->
  normalize a = Some u -> normalize b = Some v ->
  nwf u -> canonical u -> ndim u = n ->
  nwf v -> canonical v -> ndim v = n ->
  toTerm u == a -> toTerm v == b ->
  src_pow (n - k) u = tgt_pow (n - k) v ->
  exists w, nf_comp k u v = Some w /\ nwf w /\ canonical w /\ ndim w = n
            /\ toTerm w == comp k a b.
Proof.
  intros k a b n u v Ha Hb Hk Hna Hnb Hnu Hcu Hdu Hnv Hcv Hdv Hsu Hsv Hglue.
  set (c := n - k) in *.
  assert (Hcle : c <= n) by (unfold c; lia).
  assert (Hspa : toTerm (src_pow c u) == iter_src c a).
  { apply (E3_trans _ (iter_src c (toTerm u)) _).
    - apply src_pow_sound; [exact Hnu | rewrite Hdu; exact Hcle].
    - apply (iter_src_cong c (toTerm u) a n);
        [exact Hsu | rewrite <- Hdu; apply toTerm_wf; exact Hnu | exact Ha | lia]. }
  assert (Htpb : toTerm (tgt_pow c v) == iter_tgt c b).
  { apply (E3_trans _ (iter_tgt c (toTerm v)) _).
    - apply tgt_pow_sound; [exact Hnv | rewrite Hdv; exact Hcle].
    - apply (iter_tgt_cong c (toTerm v) b n);
        [exact Hsv | rewrite <- Hdv; apply toTerm_wf; exact Hnv | exact Hb | lia]. }
  assert (Hbnd : iter_src c a == iter_tgt c b).
  { apply (E3_trans _ (toTerm (src_pow c u)) _).
    - apply E2_sym; exact Hspa.
    - rewrite Hglue; exact Htpb. }
  assert (Hwfcomp : wf (comp k a b) n).
  { apply (wf_comp k a b n Ha Hb Hk). unfold c in Hbnd. exact Hbnd. }
  assert (Hnf : nf_comp k u v =
    (if NF_eqb v (idext_src c u) then Some u
     else if NF_eqb u (idext_tgt c v) then Some v else None)).
  { unfold nf_comp; cbv zeta. rewrite Hdu, Hdv, Nat.eqb_refl; simpl negb.
    assert (Hkb : (k <? n) = true) by (apply Nat.ltb_lt; exact Hk).
    rewrite Hkb; simpl negb. unfold c. reflexivity. }
  destruct (NF_eqb v (idext_src c u)) eqn:E1.
  - (* right unit IC11: result u *)
    exists u.
    split; [rewrite Hnf; reflexivity|].
    split; [exact Hnu|]. split; [exact Hcu|]. split; [exact Hdu|].
    assert (Hv : v = idext_src c u)
      by (apply NF_eqb_eq; [exact Hcv | apply idext_src_canonical; exact Hcu | exact E1]).
    assert (Hb2 : b == iter_id c (iter_src c a)).
    { apply (E3_trans _ (toTerm v) _).
      - apply E2_sym; exact Hsv.
      - rewrite Hv, toTerm_idext_src. apply iter_id_cong; exact Hspa. }
    assert (HwfR : wf (comp k a (iter_id c (iter_src c a))) n).
    { apply (wf_comp k a (iter_id c (iter_src c a)) n Ha).
      - replace n with ((n - c) + c) by lia.
        apply wf_iter_id. apply (wf_iter_src c a n); [exact Ha | exact Hcle].
      - exact Hk.
      - unfold c. apply E2_sym.
        apply (iter_tgt_id_cancel (n - k) (iter_src (n - k) a) (n - (n - k))).
        apply (wf_iter_src (n - k) a n); [exact Ha | lia]. }
    assert (HIC11 : comp k a (iter_id c (iter_src c a)) == a).
    { unfold c. apply (IC11 a k n Ha); [lia | unfold c in HwfR; exact HwfR]. }
    apply (E3_trans _ a _); [exact Hsu|]. apply E2_sym.
    apply (E3_trans _ (comp k a (iter_id c (iter_src c a))) _).
    + apply (E7_comp a a b (iter_id c (iter_src c a)) k n);
        [apply E1_refl | exact Hb2 | exact Hwfcomp | exact HwfR].
    + exact HIC11.
  - destruct (NF_eqb u (idext_tgt c v)) eqn:E2.
    + (* left unit IC12: result v *)
      exists v.
      split; [rewrite Hnf; reflexivity|].
      split; [exact Hnv|]. split; [exact Hcv|]. split; [exact Hdv|].
      assert (Hu : u = idext_tgt c v)
        by (apply NF_eqb_eq; [exact Hcu | apply idext_tgt_canonical; exact Hcv | exact E2]).
      assert (Ha2 : a == iter_id c (iter_tgt c b)).
      { apply (E3_trans _ (toTerm u) _).
        - apply E2_sym; exact Hsu.
        - rewrite Hu, toTerm_idext_tgt. apply iter_id_cong; exact Htpb. }
      assert (HwfL : wf (comp k (iter_id c (iter_tgt c b)) b) n).
      { apply (wf_comp k (iter_id c (iter_tgt c b)) b n).
        - replace n with ((n - c) + c) by lia.
          apply wf_iter_id. apply (wf_iter_tgt c b n); [exact Hb | exact Hcle].
        - exact Hb.
        - exact Hk.
        - unfold c.
          apply (iter_src_id_cancel (n - k) (iter_tgt (n - k) b) (n - (n - k))).
          apply (wf_iter_tgt (n - k) b n); [exact Hb | lia]. }
      assert (HIC12 : comp k (iter_id c (iter_tgt c b)) b == b).
      { unfold c. apply (IC12 b k n Hb); [lia | unfold c in HwfL; exact HwfL]. }
      apply (E3_trans _ b _); [exact Hsv|]. apply E2_sym.
      apply (E3_trans _ (comp k (iter_id c (iter_tgt c b)) b) _).
      * apply (E7_comp a (iter_id c (iter_tgt c b)) b b k n);
          [exact Ha2 | apply E1_refl | exact Hwfcomp | exact HwfL].
      * exact HIC12.
    + (* None: impossible by the boundary *)
      exfalso. destruct (m_comp_boundary c u v Hglue) as [HA | HB].
      * rewrite HA, NF_eqb_refl in E1; discriminate.
      * rewrite HB, NF_eqb_refl in E2; discriminate.
Qed.

(** ** Totality AND soundness of the normalizer on well-formed terms.
    The conclusion carries [toTerm u == t]: proving totality and soundness by
    the same [wf] induction is what makes the [comp] case independent of a
    free-standing [normalize_sound] (the operand soundness facts [Hsu]/[Hsv]
    that feed [nf_comp_glue] are exactly the induction hypotheses here). *)
Theorem normalize_total : forall t d,
  wf t d ->
  exists u, normalize t = Some u /\ nwf u /\ canonical u /\ ndim u = d
            /\ toTerm u == t.
Proof.
  intros t d H. induction H.
  - (* gen *)
    exists (mkNF 0 Es 0 g).
    split; [reflexivity|].
    split; [unfold nwf; cbn; lia|].
    split; [unfold canonical; cbn; reflexivity|].
    split; [unfold ndim; cbn; lia|].
    unfold toTerm; cbn [nl ne nm na]. apply E1_refl.
  - (* src e, wf e (S n) *)
    destruct IHwf as (u & Hu & Hnu & Hcu & Hdu & Hsu).
    assert (Hd : ndim u > 0) by lia.
    destruct (nf_src_spec Hnu Hd) as (w & Hsw & Hnw & Hdw & Htw).
    exists w. rewrite normalize_src_eq, Hu, Hsw.
    split; [reflexivity|].
    split; [exact Hnw|].
    split; [apply (nf_src_canonical _ _ Hcu Hsw)|].
    split; [lia|].
    (* toTerm w == src e : peel src via [Htw], then E5_src on [Hsu]. *)
    apply (E3_trans (toTerm w) (src (toTerm u)) (src e)); [exact Htw|].
    apply (E5_src (toTerm u) e n).
    + exact Hsu.
    + rewrite <- Hdu; apply toTerm_wf; exact Hnu.
    + exact H.
  - (* tgt e *)
    destruct IHwf as (u & Hu & Hnu & Hcu & Hdu & Hsu).
    assert (Hd : ndim u > 0) by lia.
    destruct (nf_tgt_spec Hnu Hd) as (w & Hsw & Hnw & Hdw & Htw).
    exists w. rewrite normalize_tgt_eq, Hu, Hsw.
    split; [reflexivity|].
    split; [exact Hnw|].
    split; [apply (nf_tgt_canonical _ _ Hcu Hsw)|].
    split; [lia|].
    apply (E3_trans (toTerm w) (tgt (toTerm u)) (tgt e)); [exact Htw|].
    apply (E6_tgt (toTerm u) e n).
    + exact Hsu.
    + rewrite <- Hdu; apply toTerm_wf; exact Hnu.
    + exact H.
  - (* id e *)
    destruct IHwf as (u & Hu & Hnu & Hcu & Hdu & Hsu).
    destruct (nf_id_spec Hnu) as (Hnw & Hdw & Htw).
    exists (nf_id u). rewrite normalize_id_eq, Hu.
    split; [reflexivity|].
    split; [exact Hnw|].
    split; [unfold canonical, nf_id; cbn [nl ne nm na]; exact Hcu|].
    split; [lia|].
    apply (E3_trans (toTerm (nf_id u)) (id (toTerm u)) (id e)); [exact Htw|].
    apply E8_id; exact Hsu.
  - (* comp k a b *)
    destruct IHwf1 as (u & Hu & Hnu & Hcu & Hdu & Hsu).
    destruct IHwf2 as (v & Hv & Hnv & Hcv & Hdv & Hsv).
    (* [Hsu : toTerm u == a] and [Hsv : toTerm v == b] now come directly from
       the induction hypotheses — no appeal to a free-standing soundness lemma,
       so totality and soundness are established by this single induction. *)
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
    destruct (nf_comp_glue _ _ _ _ _ _ H H0 H1 Hu Hv Hnu Hcu Hdu Hnv Hcv Hdv Hsu Hsv Hglue)
      as (w & Hcw & Hnw & Hcanw & Hdw & Htw).
    exists w. rewrite normalize_comp_eq, Hu, Hv. rewrite Hcw.
    split; [reflexivity|].
    split; [exact Hnw|].
    split; [exact Hcanw|].
    split; [exact Hdw|].
    exact Htw.
Qed.

Arguments normalize_total {t d}.

(** ** Soundness of the normalizer, as a corollary of [normalize_total]. *)
Theorem normalize_sound : forall t d u,
  wf t d -> normalize t = Some u -> toTerm u == t.
Proof.
  intros t d u Hwf Hn.
  destruct (normalize_total Hwf) as (u' & Hu' & _ & _ & _ & Hsu').
  rewrite Hn in Hu'. injection Hu' as ->. exact Hsu'.
Qed.
Arguments normalize_sound {t d u}.

(** ** Completeness: provable equality implies identical normal forms. *)
Theorem normalize_complete : forall t1 t2 d1 d2,
  wf t1 d1 -> wf t2 d2 -> t1 == t2 -> normalize t1 = normalize t2.
Proof.
  intros t1 t2 d1 d2 H1 H2 Heq.
  destruct (normalize_total H1) as (u & Hu & Hnu & Hcu & Hdu & Hsu).
  destruct (normalize_total H2) as (v & Hv & Hnv & Hcv & Hdv & Hsv).
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
