(** * Model.v
    A total semantic interpretation of raw terms into normal-form data,
    used to prove Lemma 4.2 (injectivity of [toTerm], i.e. [toTerm_inj]).

    The carrier is [NF] itself. Operations [m_src], [m_tgt], [m_id], [m_comp]
    are TOTAL (junk on ill-formed inputs). The point: because [interp] is
    total there is no "does it normalize" entanglement, and a single combined
    mutual induction over [eq_cat]/[wf] shows [interp] respects every axiom.
    Distinct canonical normal forms have distinct interpretations, so they are
    not provably equal. *)

Require Import Arith PeanoNat Lia Bool.
Require Import Syntax Axioms Meta NormalForm.

(** ** Total operations on the carrier [NF]. *)

Definition m_src (u : NF) : NF :=
  match nl u with
  | S l => mkNF l (ne u) (nm u) (na u)
  | 0   => mkNF 0 Es (S (nm u)) (na u)
  end.

Definition m_tgt (u : NF) : NF :=
  match nl u with
  | S l => mkNF l (ne u) (nm u) (na u)
  | 0   => mkNF 0 Et (S (nm u)) (na u)
  end.

Definition m_id (u : NF) : NF := mkNF (S (nl u)) (ne u) (nm u) (na u).

(** Total composition, mirroring [nf_comp] but returning junk (the left
    operand) instead of failing. [u] is the left operand, [v] the right. *)
Definition m_comp (k : nat) (u v : NF) : NF :=
  let n := ndim u in
  let c := n - k in
  if NF_eqb v (idext_src c u) then u
  else if NF_eqb u (idext_tgt c v) then v
  else u.

(** ** The interpretation. *)
Fixpoint interp (t : Term) : NF :=
  match t with
  | gen a      => mkNF 0 Es 0 a
  | src e      => m_src (interp e)
  | tgt e      => m_tgt (interp e)
  | id  e      => m_id (interp e)
  | comp k a b => m_comp k (interp a) (interp b)
  end.

(** ** Homomorphism lemmas for the iterated operators. *)
Lemma interp_iter_src : forall c t,
  interp (iter_src c t) = Nat.iter c m_src (interp t).
Proof.
  induction c; intros t; simpl; [reflexivity|].
  unfold iter_src in *. simpl. rewrite IHc. reflexivity.
Qed.

Lemma interp_iter_tgt : forall c t,
  interp (iter_tgt c t) = Nat.iter c m_tgt (interp t).
Proof.
  induction c; intros t; simpl; [reflexivity|].
  unfold iter_tgt in *. simpl. rewrite IHc. reflexivity.
Qed.

Lemma interp_iter_id : forall c t,
  interp (iter_id c t) = Nat.iter c m_id (interp t).
Proof.
  induction c; intros t; simpl; [reflexivity|].
  unfold iter_id in *. simpl. rewrite IHc. reflexivity.
Qed.

(** ** Recovery: interp inverts toTerm on canonical normal forms. *)

Lemma interp_iter_end_Es : forall m a,
  interp (iter_end Es m (gen a)) = mkNF 0 Es m a.
Proof.
  induction m; intros a.
  - reflexivity.
  - rewrite iter_end_S. simpl end_op. simpl interp. rewrite IHm.
    unfold m_src; cbn [nl ne nm na]. reflexivity.
Qed.

Lemma interp_iter_end_Et : forall m a,
  0 < m -> interp (iter_end Et m (gen a)) = mkNF 0 Et m a.
Proof.
  induction m; intros a Hm; [lia|].
  rewrite iter_end_S. simpl end_op. simpl interp.
  destruct m as [|m'].
  - simpl. unfold m_tgt; cbn [nl ne nm na]. reflexivity.
  - rewrite IHm by lia. unfold m_tgt; cbn [nl ne nm na]. reflexivity.
Qed.

Lemma iter_mid : forall l e m a,
  Nat.iter l m_id (mkNF 0 e m a) = mkNF l e m a.
Proof.
  induction l; intros e m a; simpl; [reflexivity|].
  rewrite IHl. unfold m_id; cbn [nl ne nm na]. reflexivity.
Qed.

Lemma interp_toTerm : forall u, canonical u -> interp (toTerm u) = u.
Proof.
  intros u Hc. unfold toTerm.
  rewrite interp_iter_id.
  assert (Hend : interp (iter_end (ne u) (nm u) (gen (na u)))
                 = mkNF 0 (ne u) (nm u) (na u)).
  { destruct (ne u) eqn:He.
    - rewrite interp_iter_end_Es. reflexivity.
    - destruct (nm u) as [|m'] eqn:Hm.
      + exfalso. unfold canonical in Hc. specialize (Hc Hm).
        rewrite Hc in He. discriminate.
      + rewrite interp_iter_end_Et by lia. reflexivity. }
  rewrite Hend. rewrite iter_mid. destruct u; reflexivity.
Qed.

(** ** Definitional unfoldings of [interp] (controlled rewriting). *)
Lemma interp_comp_eq : forall k a b, interp (comp k a b) = m_comp k (interp a) (interp b).
Proof. reflexivity. Qed.

(** ** Boolean equality facts. *)
Lemma NF_eqb_refl : forall w, NF_eqb w w = true.
Proof.
  intros w. unfold NF_eqb, Generator_eqb, End_eqb.
  rewrite !Nat.eqb_refl.
  destruct (Generator_eq_dec (na w) (na w)); [|congruence].
  destruct (nm w); cbn [andb].
  - reflexivity.
  - destruct (End_eq_dec (ne w) (ne w)); [reflexivity|congruence].
Qed.

(** ** Iterated model operators in closed form. *)
Lemma iter_m_id_eq : forall c u,
  Nat.iter c m_id u = mkNF (nl u + c) (ne u) (nm u) (na u).
Proof.
  induction c; intros u; simpl.
  - rewrite Nat.add_0_r. destruct u; reflexivity.
  - rewrite IHc. unfold m_id; cbn [nl ne nm na]. f_equal. lia.
Qed.

Lemma iter_m_src_pow : forall c u, Nat.iter c m_src u = src_pow c u.
Proof.
  induction c; intros u; simpl.
  - unfold src_pow. cbn. rewrite Nat.sub_0_r. destruct u; reflexivity.
  - rewrite IHc. unfold src_pow. destruct (c <=? nl u) eqn:E1.
    + apply Nat.leb_le in E1. unfold m_src; cbn [nl ne nm na].
      destruct (nl u - c) as [|r] eqn:Er.
      * assert (E2 : (S c <=? nl u) = false) by (apply Nat.leb_gt; lia).
        rewrite E2. f_equal. lia.
      * assert (E2 : (S c <=? nl u) = true) by (apply Nat.leb_le; lia).
        rewrite E2. f_equal. lia.
    + apply Nat.leb_gt in E1. unfold m_src; cbn [nl ne nm na].
      assert (E2 : (S c <=? nl u) = false) by (apply Nat.leb_gt; lia).
      rewrite E2. f_equal. lia.
Qed.

Lemma iter_m_tgt_pow : forall c u, Nat.iter c m_tgt u = tgt_pow c u.
Proof.
  induction c; intros u; simpl.
  - unfold tgt_pow. cbn. rewrite Nat.sub_0_r. destruct u; reflexivity.
  - rewrite IHc. unfold tgt_pow. destruct (c <=? nl u) eqn:E1.
    + apply Nat.leb_le in E1. unfold m_tgt; cbn [nl ne nm na].
      destruct (nl u - c) as [|r] eqn:Er.
      * assert (E2 : (S c <=? nl u) = false) by (apply Nat.leb_gt; lia).
        rewrite E2. f_equal. lia.
      * assert (E2 : (S c <=? nl u) = true) by (apply Nat.leb_le; lia).
        rewrite E2. f_equal. lia.
    + apply Nat.leb_gt in E1. unfold m_tgt; cbn [nl ne nm na].
      assert (E2 : (S c <=? nl u) = false) by (apply Nat.leb_gt; lia).
      rewrite E2. f_equal. lia.
Qed.

(** interp of an identity-extension is exactly the NF-level [idext]. *)
Lemma interp_idext_src : forall c t,
  interp (iter_id c (iter_src c t)) = idext_src c (interp t).
Proof.
  intros c t. rewrite interp_iter_id, interp_iter_src, iter_m_src_pow, iter_m_id_eq.
  unfold idext_src. reflexivity.
Qed.

Lemma interp_idext_tgt : forall c t,
  interp (iter_id c (iter_tgt c t)) = idext_tgt c (interp t).
Proof.
  intros c t. rewrite interp_iter_id, interp_iter_tgt, iter_m_tgt_pow, iter_m_id_eq.
  unfold idext_tgt. reflexivity.
Qed.

(** ** Dimension tracking for the model operators. *)
Lemma ndim_m_id : forall u, ndim (m_id u) = S (ndim u).
Proof. intros u. unfold ndim, m_id; cbn [nl ne nm na]. lia. Qed.

Lemma ndim_m_src : forall u, ndim u > 0 -> ndim (m_src u) = ndim u - 1.
Proof.
  intros u Hpos. unfold ndim in *. unfold m_src. destruct (nl u) as [|l].
  - cbn [nl ne nm na] in *. lia.
  - cbn [nl ne nm na] in *. lia.
Qed.

Lemma ndim_m_tgt : forall u, ndim u > 0 -> ndim (m_tgt u) = ndim u - 1.
Proof.
  intros u Hpos. unfold ndim in *. unfold m_tgt. destruct (nl u) as [|l].
  - cbn [nl ne nm na] in *. lia.
  - cbn [nl ne nm na] in *. lia.
Qed.

Lemma ndim_m_comp : forall k u v m,
  ndim u = m -> ndim v = m -> ndim (m_comp k u v) = m.
Proof.
  intros k u v m Hu Hv. unfold m_comp.
  destruct (NF_eqb v (idext_src (ndim u - k) u)); [exact Hu|].
  destruct (NF_eqb u (idext_tgt (ndim u - k) v)); [exact Hv|exact Hu].
Qed.

Lemma interp_ndim : forall t d, wf t d -> ndim (interp t) = d.
Proof.
  intros t d H. induction H.
  - unfold ndim; cbn. lia.
  - simpl. rewrite ndim_m_src by lia. lia.
  - simpl. rewrite ndim_m_tgt by lia. lia.
  - simpl. rewrite ndim_m_id. lia.
  - simpl. apply (ndim_m_comp k (interp a) (interp b) n); assumption.
Qed.

(** ** Closed forms for [src_pow]/[tgt_pow]/[idext_*]. *)
Lemma src_pow_le : forall c u, c <= nl u ->
  src_pow c u = mkNF (nl u - c) (ne u) (nm u) (na u).
Proof. intros c u H. unfold src_pow. destruct (c <=? nl u) eqn:E;
  [reflexivity | apply Nat.leb_gt in E; lia]. Qed.

Lemma src_pow_gt : forall c u, nl u < c ->
  src_pow c u = mkNF 0 Es (nm u + (c - nl u)) (na u).
Proof. intros c u H. unfold src_pow. destruct (c <=? nl u) eqn:E;
  [apply Nat.leb_le in E; lia | reflexivity]. Qed.

Lemma tgt_pow_le : forall c u, c <= nl u ->
  tgt_pow c u = mkNF (nl u - c) (ne u) (nm u) (na u).
Proof. intros c u H. unfold tgt_pow. destruct (c <=? nl u) eqn:E;
  [reflexivity | apply Nat.leb_gt in E; lia]. Qed.

Lemma tgt_pow_gt : forall c u, nl u < c ->
  tgt_pow c u = mkNF 0 Et (nm u + (c - nl u)) (na u).
Proof. intros c u H. unfold tgt_pow. destruct (c <=? nl u) eqn:E;
  [apply Nat.leb_le in E; lia | reflexivity]. Qed.

Lemma idext_src_le : forall c u, c <= nl u -> idext_src c u = u.
Proof.
  intros c u H. unfold idext_src. rewrite (src_pow_le c u H). cbn [nl ne nm na].
  replace (nl u - c + c) with (nl u) by lia. destruct u; reflexivity.
Qed.

Lemma idext_src_gt : forall c u, nl u < c ->
  idext_src c u = mkNF c Es (nm u + (c - nl u)) (na u).
Proof.
  intros c u H. unfold idext_src. rewrite (src_pow_gt c u H). cbn [nl ne nm na].
  f_equal; lia.
Qed.

Lemma idext_tgt_le : forall c u, c <= nl u -> idext_tgt c u = u.
Proof.
  intros c u H. unfold idext_tgt. rewrite (tgt_pow_le c u H). cbn [nl ne nm na].
  replace (nl u - c + c) with (nl u) by lia. destruct u; reflexivity.
Qed.

Lemma idext_tgt_gt : forall c u, nl u < c ->
  idext_tgt c u = mkNF c Et (nm u + (c - nl u)) (na u).
Proof.
  intros c u H. unfold idext_tgt. rewrite (tgt_pow_gt c u H). cbn [nl ne nm na].
  f_equal; lia.
Qed.

(** ** Soundness of [NF_eqb] on canonical normal forms. *)
Lemma NF_eqb_eq : forall u v, canonical u -> canonical v -> NF_eqb u v = true -> u = v.
Proof.
  intros [lu eu mu au] [lv ev mv av] Hcu Hcv H.
  unfold NF_eqb in H; cbn [nl ne nm na] in H.
  apply andb_true_iff in H as [H H4].
  apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H1, H2.
  unfold Generator_eqb in H3. destruct (Generator_eq_dec au av) as [Ha|]; [|discriminate].
  subst lv mv av.
  assert (eu = ev) as He.
  { unfold canonical in *; cbn [nm ne] in *.
    destruct mu as [|m'].
    - rewrite (Hcu eq_refl), (Hcv eq_refl); reflexivity.
    - unfold End_eqb in H4. destruct (End_eq_dec eu ev); [assumption|discriminate]. }
  subst ev. reflexivity.
Qed.

(** ** Lemma 4.4 (model form): a matched boundary forces a unit pattern. *)
Lemma m_comp_boundary : forall c u v,
  src_pow c u = tgt_pow c v -> v = idext_src c u \/ u = idext_tgt c v.
Proof.
  intros c u v H.
  destruct (le_gt_dec c (nl u)) as [Hu|Hu]; destruct (le_gt_dec c (nl v)) as [Hv|Hv].
  - (* both le : u = v *)
    left. rewrite (src_pow_le c u Hu), (tgt_pow_le c v Hv) in H.
    injection H as Hl He Hm Ha. rewrite (idext_src_le c u Hu).
    destruct u as [lu eu mu au], v as [lv ev mv av]; cbn [nl ne nm na] in *.
    subst. f_equal. lia.
  - (* c<=nl u, c>nl v : u = idext_tgt c v *)
    right. rewrite (src_pow_le c u Hu), (tgt_pow_gt c v Hv) in H.
    rewrite (idext_tgt_gt c v Hv).
    destruct u as [lu eu mu au], v as [lv ev mv av]; cbn [nl ne nm na] in *.
    injection H as Hl He Hm Ha. subst. f_equal. lia.
  - (* c>nl u, c<=nl v : v = idext_src c u *)
    left. rewrite (src_pow_gt c u Hu), (tgt_pow_le c v Hv) in H.
    rewrite (idext_src_gt c u Hu).
    destruct u as [lu eu mu au], v as [lv ev mv av]; cbn [nl ne nm na] in *.
    injection H as Hl He Hm Ha. subst. f_equal. lia.
  - (* both gt : impossible, Es = Et *)
    rewrite (src_pow_gt c u Hu), (tgt_pow_gt c v Hv) in H.
    injection H as He Hm Ha. discriminate He.
Qed.

(** ** Canonicity and identities for [idext_*]. *)
Lemma idext_src_canonical : forall c u, canonical u -> canonical (idext_src c u).
Proof.
  intros c u Hc. destruct (le_gt_dec c (nl u)) as [Hle|Hgt].
  - rewrite (idext_src_le c u Hle). exact Hc.
  - rewrite (idext_src_gt c u Hgt). unfold canonical; cbn [nm ne]. intros _; reflexivity.
Qed.

Lemma idext_tgt_canonical : forall c u, canonical u -> canonical (idext_tgt c u).
Proof.
  intros c u Hc. destruct (le_gt_dec c (nl u)) as [Hle|Hgt].
  - rewrite (idext_tgt_le c u Hle). exact Hc.
  - rewrite (idext_tgt_gt c u Hgt). unfold canonical; cbn [nm ne].
    intro H0; exfalso; lia.
Qed.

Lemma idext_tgt_nl : forall c v, nl (idext_tgt c v) = nl (tgt_pow c v) + c.
Proof. intros c v. unfold idext_tgt. cbn [nl]. reflexivity. Qed.

Lemma idext_src_idext_tgt : forall c v, idext_src c (idext_tgt c v) = idext_tgt c v.
Proof. intros c v. apply idext_src_le. rewrite idext_tgt_nl. lia. Qed.

Lemma idext_src_nl : forall c w, nl (idext_src c w) = nl (src_pow c w) + c.
Proof. intros c w. unfold idext_src. cbn [nl]. reflexivity. Qed.

Lemma idext_src_idem : forall c w, idext_src c (idext_src c w) = idext_src c w.
Proof. intros c w. apply idext_src_le. rewrite idext_src_nl. lia. Qed.

Lemma idext_tgt_idem : forall c w, idext_tgt c (idext_tgt c w) = idext_tgt c w.
Proof. intros c w. apply idext_tgt_le. rewrite idext_tgt_nl. lia. Qed.

(** ** Value of [m_comp] under a unit pattern. *)
Lemma m_comp_right : forall k u v,
  v = idext_src (ndim u - k) u -> m_comp k u v = u.
Proof.
  intros k u v Hv. unfold m_comp; cbv zeta. rewrite Hv, NF_eqb_refl. reflexivity.
Qed.

Lemma m_comp_left : forall k u v, canonical u -> canonical v ->
  u = idext_tgt (ndim u - k) v -> m_comp k u v = v.
Proof.
  intros k u v Hcu Hcv Hu. unfold m_comp; cbv zeta. set (c := ndim u - k) in *.
  destruct (NF_eqb v (idext_src c u)) eqn:E1.
  - apply NF_eqb_eq in E1; [| exact Hcv | apply idext_src_canonical; exact Hcu].
    rewrite Hu in E1. rewrite idext_src_idext_tgt in E1. rewrite <- Hu in E1.
    symmetry; exact E1.
  - destruct (NF_eqb u (idext_tgt c v)) eqn:E2.
    + reflexivity.
    + rewrite Hu, NF_eqb_refl in E2. discriminate.
Qed.

Lemma m_comp_idsrc : forall n d u v,
  ndim u = d -> v = idext_src (d - n) u -> m_comp n u v = u.
Proof. intros n d u v Hd Hv. apply m_comp_right. rewrite Hd. exact Hv. Qed.

Lemma m_comp_idtgt : forall n d u v,
  ndim u = d -> canonical u -> canonical v ->
  u = idext_tgt (d - n) v -> m_comp n u v = v.
Proof. intros n d u v Hd Hcu Hcv Hu. apply m_comp_left; try assumption. rewrite Hd. exact Hu. Qed.

(** Self-composition is degenerate: every branch of [m_comp] returns the left
    operand, so [m_comp k u u = u] unconditionally. *)
Lemma m_comp_diag : forall k u, m_comp k u u = u.
Proof.
  intros k u. unfold m_comp; cbv zeta.
  destruct (NF_eqb u (idext_src (ndim u - k) u)); [reflexivity|].
  destruct (NF_eqb u (idext_tgt (ndim u - k) u)); reflexivity.
Qed.

(** ** [interp] always lands in canonical normal forms. *)
Lemma m_src_canonical : forall w, canonical w -> canonical (m_src w).
Proof.
  intros w Hc. unfold m_src. destruct (nl w).
  - unfold canonical; cbn [nm ne]. intro H0; discriminate.
  - unfold canonical in *; cbn [nm ne] in *. exact Hc.
Qed.

Lemma m_tgt_canonical : forall w, canonical w -> canonical (m_tgt w).
Proof.
  intros w Hc. unfold m_tgt. destruct (nl w).
  - unfold canonical; cbn [nm ne]. intro H0; discriminate.
  - unfold canonical in *; cbn [nm ne] in *. exact Hc.
Qed.

Lemma m_id_canonical : forall w, canonical w -> canonical (m_id w).
Proof. intros w Hc. unfold m_id, canonical in *; cbn [nm ne] in *. exact Hc. Qed.

Lemma m_comp_canonical : forall k u v,
  canonical u -> canonical v -> canonical (m_comp k u v).
Proof.
  intros k u v Hu Hv. unfold m_comp; cbv zeta.
  destruct (NF_eqb v (idext_src (ndim u - k) u)); [exact Hu|].
  destruct (NF_eqb u (idext_tgt (ndim u - k) v)); [exact Hv|exact Hu].
Qed.

Lemma interp_canonical : forall t, canonical (interp t).
Proof.
  induction t; simpl.
  - unfold canonical; cbn. reflexivity.
  - apply m_src_canonical; exact IHt.
  - apply m_tgt_canonical; exact IHt.
  - apply m_id_canonical; exact IHt.
  - apply m_comp_canonical; assumption.
Qed.

(** ** Interaction of [m_src]/[m_tgt] with identity-extensions. *)
Lemma iter_succ_r : forall (f : NF -> NF) c x, Nat.iter (S c) f x = Nat.iter c f (f x).
Proof.
  intros f c x. revert x. induction c; intro x.
  - reflexivity.
  - change (Nat.iter (S (S c)) f x) with (f (Nat.iter (S c) f x)).
    rewrite IHc. reflexivity.
Qed.

Lemma m_src_m_id : forall w, m_src (m_id w) = w.
Proof. intros w. unfold m_src, m_id; cbn [nl ne nm na]. destruct w; reflexivity. Qed.

Lemma m_tgt_m_id : forall w, m_tgt (m_id w) = w.
Proof. intros w. unfold m_tgt, m_id; cbn [nl ne nm na]. destruct w; reflexivity. Qed.

Lemma idext_src_iter : forall c w, idext_src c w = Nat.iter c m_id (Nat.iter c m_src w).
Proof. intros c w. rewrite iter_m_src_pow, iter_m_id_eq. unfold idext_src. reflexivity. Qed.

Lemma idext_tgt_iter : forall c w, idext_tgt c w = Nat.iter c m_id (Nat.iter c m_tgt w).
Proof. intros c w. rewrite iter_m_tgt_pow, iter_m_id_eq. unfold idext_tgt. reflexivity. Qed.

Lemma m_src_idext_src_S : forall c w, m_src (idext_src (S c) w) = idext_src c (m_src w).
Proof.
  intros c w. rewrite !idext_src_iter.
  change (Nat.iter (S c) m_id (Nat.iter (S c) m_src w))
    with (m_id (Nat.iter c m_id (Nat.iter (S c) m_src w))).
  rewrite m_src_m_id. rewrite (iter_succ_r m_src c w). reflexivity.
Qed.

Lemma m_tgt_idext_tgt_S : forall c w, m_tgt (idext_tgt (S c) w) = idext_tgt c (m_tgt w).
Proof.
  intros c w. rewrite !idext_tgt_iter.
  change (Nat.iter (S c) m_id (Nat.iter (S c) m_tgt w))
    with (m_id (Nat.iter c m_id (Nat.iter (S c) m_tgt w))).
  rewrite m_tgt_m_id. rewrite (iter_succ_r m_tgt c w). reflexivity.
Qed.

Lemma idext_src_0 : forall w, idext_src 0 w = w.
Proof. intros w. apply idext_src_le. lia. Qed.

Lemma idext_tgt_0 : forall w, idext_tgt 0 w = w.
Proof. intros w. apply idext_tgt_le. lia. Qed.

Lemma m_id_idext_src : forall c w, m_id (idext_src c w) = idext_src (S c) (m_id w).
Proof.
  intros c w. rewrite !idext_src_iter.
  rewrite (iter_succ_r m_src c (m_id w)), m_src_m_id. reflexivity.
Qed.

Lemma m_id_idext_tgt : forall c w, m_id (idext_tgt c w) = idext_tgt (S c) (m_id w).
Proof.
  intros c w. rewrite !idext_tgt_iter.
  rewrite (iter_succ_r m_tgt c (m_id w)), m_tgt_m_id. reflexivity.
Qed.

Lemma ndim_m_id_eq : forall u, ndim (m_id u) = S (ndim u).
Proof. exact ndim_m_id. Qed.

(** src/tgt agree once they have to strip an id (model IC1/IC2). *)
Lemma m_tgt_m_src : forall w, m_tgt (m_src w) = m_tgt (m_tgt w).
Proof. intros w. unfold m_src, m_tgt. destruct (nl w); reflexivity. Qed.

Lemma m_src_m_tgt : forall w, m_src (m_tgt w) = m_src (m_src w).
Proof. intros w. unfold m_src, m_tgt. destruct (nl w); reflexivity. Qed.

Lemma m_src_idext_tgt_S : forall c w, m_src (idext_tgt (S c) w) = idext_tgt c (m_tgt w).
Proof.
  intros c w. rewrite !idext_tgt_iter.
  change (Nat.iter (S c) m_id (Nat.iter (S c) m_tgt w))
    with (m_id (Nat.iter c m_id (Nat.iter (S c) m_tgt w))).
  rewrite m_src_m_id, (iter_succ_r m_tgt c w). reflexivity.
Qed.

Lemma m_tgt_idext_src_S : forall c w, m_tgt (idext_src (S c) w) = idext_src c (m_src w).
Proof.
  intros c w. rewrite !idext_src_iter.
  change (Nat.iter (S c) m_id (Nat.iter (S c) m_src w))
    with (m_id (Nat.iter c m_id (Nat.iter (S c) m_src w))).
  rewrite m_tgt_m_id, (iter_succ_r m_src c w). reflexivity.
Qed.

Lemma idext_tgt_collapse : forall j w, idext_tgt (S j) (m_src w) = idext_tgt (S j) (m_tgt w).
Proof.
  intros j w. rewrite !idext_tgt_iter. f_equal.
  rewrite (iter_succ_r m_tgt j (m_src w)), (iter_succ_r m_tgt j (m_tgt w)), m_tgt_m_src.
  reflexivity.
Qed.

Lemma idext_src_collapse : forall j w, idext_src (S j) (m_tgt w) = idext_src (S j) (m_src w).
Proof.
  intros j w. rewrite !idext_src_iter. f_equal.
  rewrite (iter_succ_r m_src j (m_tgt w)), (iter_succ_r m_src j (m_src w)), m_src_m_tgt.
  reflexivity.
Qed.

(** ** Identity-extension tower normalization.
    For nested identity-extensions the LARGER codimension wins (absorbs the
    smaller). These let an [idext] tower collapse to a single extension. *)

Lemma iter_add : forall (f : NF -> NF) a b x,
  Nat.iter (a + b) f x = Nat.iter a f (Nat.iter b f x).
Proof. intros f a b x. induction a; simpl; [reflexivity | rewrite IHa; reflexivity]. Qed.

Lemma iter_msrc_mid_cancel : forall c Z, Nat.iter c m_src (Nat.iter c m_id Z) = Z.
Proof.
  induction c; intros Z; [reflexivity|].
  change (Nat.iter (S c) m_id Z) with (m_id (Nat.iter c m_id Z)).
  rewrite (iter_succ_r m_src c (m_id (Nat.iter c m_id Z))), m_src_m_id. apply IHc.
Qed.

Lemma iter_mtgt_mid_cancel : forall c Z, Nat.iter c m_tgt (Nat.iter c m_id Z) = Z.
Proof.
  induction c; intros Z; [reflexivity|].
  change (Nat.iter (S c) m_id Z) with (m_id (Nat.iter c m_id Z)).
  rewrite (iter_succ_r m_tgt c (m_id (Nat.iter c m_id Z))), m_tgt_m_id. apply IHc.
Qed.

Lemma iter_split_src : forall c1 c2 X, c2 <= c1 ->
  Nat.iter c1 m_src X = Nat.iter (c1 - c2) m_src (Nat.iter c2 m_src X).
Proof. intros c1 c2 X H. rewrite <- iter_add. f_equal. lia. Qed.

Lemma iter_split_tgt : forall c1 c2 X, c2 <= c1 ->
  Nat.iter c1 m_tgt X = Nat.iter (c1 - c2) m_tgt (Nat.iter c2 m_tgt X).
Proof. intros c1 c2 X H. rewrite <- iter_add. f_equal. lia. Qed.

Lemma iter_msrc_over_mid : forall c1 c2 W, c2 <= c1 ->
  Nat.iter c1 m_src (Nat.iter c2 m_id W) = Nat.iter (c1 - c2) m_src W.
Proof.
  intros c1 c2 W H.
  rewrite (iter_split_src c1 c2 (Nat.iter c2 m_id W) H), iter_msrc_mid_cancel. reflexivity.
Qed.

Lemma iter_mtgt_over_mid : forall c1 c2 W, c2 <= c1 ->
  Nat.iter c1 m_tgt (Nat.iter c2 m_id W) = Nat.iter (c1 - c2) m_tgt W.
Proof.
  intros c1 c2 W H.
  rewrite (iter_split_tgt c1 c2 (Nat.iter c2 m_id W) H), iter_mtgt_mid_cancel. reflexivity.
Qed.

(** Absorption: outer (smaller-or-equal codim) is swallowed by the inner. *)
Lemma ab_ss : forall c1 c2 X, c1 <= c2 -> idext_src c1 (idext_src c2 X) = idext_src c2 X.
Proof. intros c1 c2 X H. apply idext_src_le. rewrite idext_src_nl. lia. Qed.
Lemma ab_st : forall c1 c2 X, c1 <= c2 -> idext_src c1 (idext_tgt c2 X) = idext_tgt c2 X.
Proof. intros c1 c2 X H. apply idext_src_le. rewrite idext_tgt_nl. lia. Qed.
Lemma ab_ts : forall c1 c2 X, c1 <= c2 -> idext_tgt c1 (idext_src c2 X) = idext_src c2 X.
Proof. intros c1 c2 X H. apply idext_tgt_le. rewrite idext_src_nl. lia. Qed.
Lemma ab_tt : forall c1 c2 X, c1 <= c2 -> idext_tgt c1 (idext_tgt c2 X) = idext_tgt c2 X.
Proof. intros c1 c2 X H. apply idext_tgt_le. rewrite idext_tgt_nl. lia. Qed.

(** Override (outer larger codim, same op): outer wins, inner skipped. *)
Lemma ov_ss : forall c1 c2 X, c2 <= c1 -> idext_src c1 (idext_src c2 X) = idext_src c1 X.
Proof.
  intros c1 c2 X H.
  rewrite (idext_src_iter c1 (idext_src c2 X)), (idext_src_iter c2 X), (idext_src_iter c1 X).
  f_equal. rewrite iter_msrc_over_mid by lia. rewrite (iter_split_src c1 c2 X H). reflexivity.
Qed.
Lemma ov_tt : forall c1 c2 X, c2 <= c1 -> idext_tgt c1 (idext_tgt c2 X) = idext_tgt c1 X.
Proof.
  intros c1 c2 X H.
  rewrite (idext_tgt_iter c1 (idext_tgt c2 X)), (idext_tgt_iter c2 X), (idext_tgt_iter c1 X).
  f_equal. rewrite iter_mtgt_over_mid by lia. rewrite (iter_split_tgt c1 c2 X H). reflexivity.
Qed.

(** Override (outer larger codim, mixed op): outer wins, needs strict <. *)
Lemma ov_st : forall c1 c2 X, c2 < c1 -> idext_src c1 (idext_tgt c2 X) = idext_src c1 X.
Proof.
  intros c1 c2 X H. destruct (le_gt_dec c2 (nl X)) as [Hle|Hgt].
  - rewrite (idext_tgt_le c2 X Hle). reflexivity.
  - rewrite (idext_tgt_gt c2 X Hgt).
    rewrite (idext_src_gt c1 (mkNF c2 Et (nm X + (c2 - nl X)) (na X))) by (cbn [nl]; lia).
    rewrite (idext_src_gt c1 X) by lia.
    cbn [nl ne nm na]. f_equal. lia.
Qed.
Lemma ov_ts : forall c1 c2 X, c2 < c1 -> idext_tgt c1 (idext_src c2 X) = idext_tgt c1 X.
Proof.
  intros c1 c2 X H. destruct (le_gt_dec c2 (nl X)) as [Hle|Hgt].
  - rewrite (idext_src_le c2 X Hle). reflexivity.
  - rewrite (idext_src_gt c2 X Hgt).
    rewrite (idext_tgt_gt c1 (mkNF c2 Es (nm X + (c2 - nl X)) (na X))) by (cbn [nl]; lia).
    rewrite (idext_tgt_gt c1 X) by lia.
    cbn [nl ne nm na]. f_equal. lia.
Qed.

(** NF discreteness for identity-extensions (for IC10 contradiction branches). *)
Lemma idext_src_codim_inj : forall c1 c2 X,
  nl X < c1 -> nl X < c2 -> idext_src c1 X = idext_src c2 X -> c1 = c2.
Proof.
  intros c1 c2 X H1 H2 He.
  rewrite (idext_src_gt c1 X H1), (idext_src_gt c2 X H2) in He.
  injection He; auto.
Qed.

Lemma idext_tgt_codim_inj : forall c1 c2 X,
  nl X < c1 -> nl X < c2 -> idext_tgt c1 X = idext_tgt c2 X -> c1 = c2.
Proof.
  intros c1 c2 X H1 H2 He.
  rewrite (idext_tgt_gt c1 X H1), (idext_tgt_gt c2 X H2) in He.
  injection He; auto.
Qed.

Lemma idext_src_tgt_disc : forall c1 c2 X,
  nl X < c1 -> nl X < c2 -> idext_src c1 X = idext_tgt c2 X -> False.
Proof.
  intros c1 c2 X H1 H2 He.
  rewrite (idext_src_gt c1 X H1), (idext_tgt_gt c2 X H2) in He.
  injection He; intros; discriminate.
Qed.

(** For each identity-extension in the goal, decide its codim against the base's
    nl (guarded so we never re-split the same one), then collapse the small ones. *)
Ltac splitnl :=
  repeat
    (match goal with
     | [ |- context[idext_src ?c ?X] ] =>
         lazymatch goal with
         | [ _ : c <= nl X |- _ ] => fail
         | [ _ : nl X < c |- _ ] => fail
         | _ => destruct (le_gt_dec c (nl X))
         end
     | [ |- context[idext_tgt ?c ?X] ] =>
         lazymatch goal with
         | [ _ : c <= nl X |- _ ] => fail
         | [ _ : nl X < c |- _ ] => fail
         | _ => destruct (le_gt_dec c (nl X))
         end
     end);
  repeat (rewrite idext_src_le by assumption || rewrite idext_tgt_le by assumption).

(** ** Dimension of an identity-extension.
    Whenever the codimension is within the dimension budget [c <= ndim u], an
    identity-extension preserves dimension. (When [c > ndim u] truncation can
    occur, but [c <= ndim u] forces the no-truncation branch.) *)
Lemma ndim_idext_src : forall c u, c <= ndim u -> ndim (idext_src c u) = ndim u.
Proof.
  intros c u H. unfold idext_src, src_pow.
  destruct (c <=? nl u) eqn:E; unfold ndim in *; cbn [nl ne nm na] in *.
  - apply Nat.leb_le in E. lia.
  - apply Nat.leb_gt in E. lia.
Qed.

Lemma ndim_idext_tgt : forall c u, c <= ndim u -> ndim (idext_tgt c u) = ndim u.
Proof.
  intros c u H. unfold idext_tgt, tgt_pow.
  destruct (c <=? nl u) eqn:E; unfold ndim in *; cbn [nl ne nm na] in *.
  - apply Nat.leb_le in E. lia.
  - apply Nat.leb_gt in E. lia.
Qed.

(** A composite whose two unit tests both fail (the "junk" else branch of
    [m_comp]) returns its left operand, provided the only way its left operand
    could be a target-unit of the right is when the two operands coincide.
    This handles the residual case the IC10 exchange leaves behind. *)
Lemma m_comp_junk : forall k u v, canonical u -> canonical v ->
  (u = idext_tgt (ndim u - k) v -> v = u) -> m_comp k u v = u.
Proof.
  intros k u v Hu Hv Himp. unfold m_comp; cbv zeta.
  destruct (NF_eqb v (idext_src (ndim u - k) u)) eqn:E1; [reflexivity|].
  destruct (NF_eqb u (idext_tgt (ndim u - k) v)) eqn:E2; [|reflexivity].
  apply NF_eqb_eq in E2; [| exact Hu | apply idext_tgt_canonical; exact Hv].
  apply Himp; exact E2.
Qed.

(** ** The five residual IC10 (exchange) leaves, over an arbitrary canonical
    base [B] with [ndim B = d]. Each is one of the boundary-collapse cases left
    by the tower-normalization block. *)

Lemma ic10_l1 : forall m n d B, canonical B -> ndim B = d -> d - n > d - m ->
  idext_src (d - m) B = m_comp n (idext_src (d - m) B) (idext_src (d - n) B).
Proof.
  intros m n d B HB Hd Hc. symmetry.
  apply (m_comp_idsrc n d (idext_src (d - m) B) (idext_src (d - n) B)).
  - rewrite ndim_idext_src by (rewrite Hd; lia). exact Hd.
  - symmetry. apply ov_ss. lia.
Qed.

Lemma ic10_l2 : forall m n d B, canonical B -> ndim B = d -> d - n <= d - m ->
  m_comp m (idext_src (d - n) B) (idext_src (d - m) B) = idext_src (d - n) B.
Proof.
  intros m n d B HB Hd Hc.
  apply (m_comp_idsrc m d (idext_src (d - n) B) (idext_src (d - m) B)).
  - rewrite ndim_idext_src by (rewrite Hd; lia). exact Hd.
  - symmetry. apply ov_ss. lia.
Qed.

Lemma ic10_l4 : forall m n d B, canonical B -> ndim B = d -> d - n > d - m ->
  idext_src (d - m) B = m_comp n (idext_tgt (d - n) B) (idext_src (d - m) B).
Proof.
  intros m n d B HB Hd Hc. symmetry.
  apply (m_comp_idtgt n d (idext_tgt (d - n) B) (idext_src (d - m) B)).
  - rewrite ndim_idext_tgt by (rewrite Hd; lia). exact Hd.
  - apply idext_tgt_canonical; exact HB.
  - apply idext_src_canonical; exact HB.
  - symmetry. apply ov_ts. lia.
Qed.

Lemma ic10_l5 : forall m n d B, canonical B -> ndim B = d -> d - n <= d - m ->
  m_comp m (idext_tgt (d - m) (idext_src (d - n) B)) (idext_src (d - n) B)
  = idext_src (d - n) B.
Proof.
  intros m n d B HB Hd Hc.
  assert (Hinner : ndim (idext_src (d - n) B) = d)
    by (rewrite ndim_idext_src by (rewrite Hd; lia); exact Hd).
  apply (m_comp_idtgt m d (idext_tgt (d - m) (idext_src (d - n) B))
                          (idext_src (d - n) B)).
  - rewrite ndim_idext_tgt by (rewrite Hinner; lia). exact Hinner.
  - apply idext_tgt_canonical, idext_src_canonical; exact HB.
  - apply idext_src_canonical; exact HB.
  - reflexivity.
Qed.

Lemma ic10_l3 : forall m n d B, canonical B -> ndim B = d -> d - n > d - m ->
  m_comp m (idext_src (d - m) B) (idext_tgt (d - n) B)
  = m_comp n (idext_tgt (d - n) B) (idext_src (d - m) B).
Proof.
  intros m n d B HB Hd Hc.
  assert (HR : m_comp n (idext_tgt (d - n) B) (idext_src (d - m) B)
               = idext_src (d - m) B).
  { apply (m_comp_idtgt n d).
    - rewrite ndim_idext_tgt by (rewrite Hd; lia). exact Hd.
    - apply idext_tgt_canonical; exact HB.
    - apply idext_src_canonical; exact HB.
    - symmetry. apply ov_ts. lia. }
  rewrite HR.
  apply m_comp_junk.
  - apply idext_src_canonical; exact HB.
  - apply idext_tgt_canonical; exact HB.
  - intro H.
    rewrite ndim_idext_src in H by (rewrite Hd; lia).
    rewrite Hd in H. rewrite ab_tt in H by lia.
    symmetry; exact H.
Qed.

(** ** Combined mutual induction principle for [eq_cat] and [wf]. *)
Scheme eq_cat_min := Minimality for eq_cat Sort Prop
  with wf_min := Minimality for wf Sort Prop.
Combined Scheme eq_cat_wf_mut from eq_cat_min, wf_min.

(** The wf-carried invariant: model-level boundary for compositions. *)
(** Recursive model well-formedness: every nested composition's boundary
    matches at the model level. This is what lets the IC9/IC10 cases reach
    the boundaries of the *inner* composites. *)
Fixpoint Qwf (t : Term) (d : nat) : Prop :=
  match t with
  | gen _      => True
  | src e      => Qwf e (S d)
  | tgt e      => Qwf e (S d)
  | id  e      => match d with 0 => True | S n => Qwf e n end
  | comp k a b => src_pow (d - k) (interp a) = tgt_pow (d - k) (interp b)
                  /\ Qwf a d /\ Qwf b d
  end.

(** The top boundary in [src_pow]/[tgt_pow] form. *)
Lemma Qwf_boundary : forall k a b d, Qwf (comp k a b) d ->
  src_pow (d - k) (interp a) = tgt_pow (d - k) (interp b).
Proof. intros k a b d H. exact (proj1 H). Qed.

(** Resolve a composite whose boundary's unit pattern is a hypothesis, in all
    hypotheses and the goal. Used to flatten the IC10 (exchange) case tree. *)
Ltac mres :=
  repeat
    ((erewrite m_comp_idsrc in * by eassumption)
     || (erewrite m_comp_idtgt in * by (eassumption || apply interp_canonical))).

(** Resolve the one composite pinned by boundary equation [E], in all hyps + goal. *)
Ltac mres1 E :=
  try first
    [ erewrite (m_comp_idsrc _ _ _ _ _ E) in * by eassumption
    | erewrite (m_comp_idtgt _ _ _ _ _ _ _ E) in * by (eauto using interp_canonical) ].

(** Resolve the composite pinned by [E] inside hypothesis [H]. *)
Ltac mresH H E :=
  try first
    [ erewrite (m_comp_idsrc _ _ _ _ _ E) in H by eassumption
    | erewrite (m_comp_idtgt _ _ _ _ _ _ _ E) in H by (eauto using interp_canonical) ].

(** Repeatedly resolve any composite pinned by a boundary equation in context. *)
Ltac mstep :=
  match goal with
  | [ E : ?v = idext_src ?c ?u |- _ ] =>
      erewrite (m_comp_idsrc _ _ u v _ E) in * by eassumption
  | [ E : ?u = idext_tgt ?c ?v |- _ ] =>
      erewrite (m_comp_idtgt _ _ u v _ _ _ E) in *
        by (first [ eassumption | apply interp_canonical ])
  end.
Ltac mresall := repeat mstep.

(** Goal-directed: resolve a composite in the goal whose operands have a
    matching boundary equation in context. *)
Ltac gres :=
  repeat
    match goal with
    | [ E : ?v = idext_src ?c ?u |- context[m_comp ?k ?u ?v] ] =>
        rewrite (m_comp_idsrc k _ u v ltac:(eassumption) E)
    | [ E : ?u = idext_tgt ?c ?v |- context[m_comp ?k ?u ?v] ] =>
        rewrite (m_comp_idtgt k _ u v ltac:(eassumption)
                   (interp_canonical _) (interp_canonical _) E)
    end.

(** ** Model soundness: [interp] respects provable equality.
    Proved by the combined mutual induction; the [comp] axiom cases (IC5–IC13)
    are the substantive content. The IC10 (exchange) case reduces, after
    tower-normalization, to the five boundary-collapse leaves discharged by
    [ic10_l1]–[ic10_l5] above. *)
Theorem interp_sound_mut :
  (forall x y, x == y -> interp x = interp y)
  /\ (forall t d, wf t d -> Qwf t d).
Proof.
  apply eq_cat_wf_mut.
  - (* E1 refl *) intros x. reflexivity.
  - (* E2 sym *) intros x y _ IH. symmetry; exact IH.
  - (* E3 trans *) intros x y z _ IH1 _ IH2. rewrite IH1; exact IH2.
  - (* E5 src *) intros x y n _ IH _ _. simpl. rewrite IH. reflexivity.
  - (* E6 tgt *) intros x y n _ IH _ _. simpl. rewrite IH. reflexivity.
  - (* E7 comp *) intros x y z w n d _ IHxy _ IHzw _ _. simpl. rewrite IHxy, IHzw. reflexivity.
  - (* E8 id *) intros x y _ IH. simpl. rewrite IH. reflexivity.
  - (* IC1 *) intros x n _ _.
    simpl. unfold m_src, m_tgt. destruct (nl (interp x)) as [|[|l]]; reflexivity.
  - (* IC2 *) intros x n _ _.
    simpl. unfold m_src, m_tgt. destruct (nl (interp x)) as [|[|l]]; reflexivity.
  - (* IC3 src(id x) = x *) intros x n _.
    simpl. unfold m_src, m_id; cbn [nl ne nm na]. destruct (interp x); reflexivity.
  - (* IC4 tgt(id x) = x *) intros x n _.
    simpl. unfold m_tgt, m_id; cbn [nl ne nm na]. destruct (interp x); reflexivity.
  - (* IC5 src(comp) = src x *) intros x y n Hwf IHwf.
    apply wf_comp_inv in Hwf. destruct Hwf as (Hy & Hx & Hk & Hbnd).
    apply Qwf_boundary in IHwf. replace (S n - n) with 1 in IHwf by lia.
    pose proof (interp_ndim _ _ Hy) as Hny.
    cbn [interp].
    destruct (m_comp_boundary 1 (interp y) (interp x) IHwf) as [HA | HB].
    + rewrite (m_comp_right n (interp y) (interp x)).
      2:{ rewrite Hny. replace (S n - n) with 1 by lia. exact HA. }
      rewrite HA, m_src_idext_src_S, idext_src_0. reflexivity.
    + rewrite (m_comp_left n (interp y) (interp x)).
      * reflexivity.
      * apply interp_canonical.
      * apply interp_canonical.
      * rewrite Hny. replace (S n - n) with 1 by lia. exact HB.
  - (* IC6 tgt(comp) = tgt y *) intros x y n Hwf IHwf.
    apply wf_comp_inv in Hwf. destruct Hwf as (Hy & Hx & Hk & Hbnd).
    apply Qwf_boundary in IHwf. replace (S n - n) with 1 in IHwf by lia.
    pose proof (interp_ndim _ _ Hy) as Hny.
    cbn [interp].
    destruct (m_comp_boundary 1 (interp y) (interp x) IHwf) as [HA | HB].
    + rewrite (m_comp_right n (interp y) (interp x)).
      * reflexivity.
      * rewrite Hny. replace (S n - n) with 1 by lia. exact HA.
    + rewrite (m_comp_left n (interp y) (interp x)).
      2: apply interp_canonical.
      2: apply interp_canonical.
      2:{ rewrite Hny. replace (S n - n) with 1 by lia. exact HB. }
      rewrite HB, m_tgt_idext_tgt_S, idext_tgt_0. reflexivity.
  - (* IC7 src(comp) = comp(src)(src) *) intros x y n d Hwf IHwf Hd.
    apply wf_comp_inv in Hwf. destruct Hwf as (Hy & Hx & Hk & Hbnd).
    apply Qwf_boundary in IHwf.
    pose proof (interp_ndim _ _ Hy) as Hny.
    cbn [interp].
    destruct (d - n) as [|[|c'']] eqn:Hc; try lia.
    destruct (m_comp_boundary (S (S c'')) (interp y) (interp x) IHwf) as [HA | HB].
    + rewrite (m_comp_right n (interp y) (interp x)).
      2:{ rewrite Hny, Hc. exact HA. }
      rewrite HA, m_src_idext_src_S.
      rewrite (m_comp_right n (m_src (interp y)) (idext_src (S c'') (m_src (interp y)))).
      2:{ rewrite ndim_m_src by (rewrite Hny; lia). rewrite Hny.
          replace (d - 1 - n) with (S c'') by lia. reflexivity. }
      reflexivity.
    + rewrite (m_comp_left n (interp y) (interp x)).
      2: apply interp_canonical.
      2: apply interp_canonical.
      2:{ rewrite Hny, Hc. exact HB. }
      rewrite (m_comp_left n (m_src (interp y)) (m_src (interp x))).
      * reflexivity.
      * apply m_src_canonical; apply interp_canonical.
      * apply m_src_canonical; apply interp_canonical.
      * rewrite ndim_m_src by (rewrite Hny; lia). rewrite Hny.
        replace (d - 1 - n) with (S c'') by lia.
        rewrite HB, m_src_idext_tgt_S. symmetry; apply idext_tgt_collapse.
  - (* IC8 tgt(comp) = comp(tgt)(tgt) *) intros x y n d Hwf IHwf Hd.
    apply wf_comp_inv in Hwf. destruct Hwf as (Hy & Hx & Hk & Hbnd).
    apply Qwf_boundary in IHwf.
    pose proof (interp_ndim _ _ Hy) as Hny.
    cbn [interp].
    destruct (d - n) as [|[|c'']] eqn:Hc; try lia.
    destruct (m_comp_boundary (S (S c'')) (interp y) (interp x) IHwf) as [HA | HB].
    + rewrite (m_comp_right n (interp y) (interp x)).
      2:{ rewrite Hny, Hc. exact HA. }
      rewrite (m_comp_right n (m_tgt (interp y)) (m_tgt (interp x))).
      * reflexivity.
      * rewrite ndim_m_tgt by (rewrite Hny; lia). rewrite Hny.
        replace (d - 1 - n) with (S c'') by lia.
        rewrite HA, m_tgt_idext_src_S. symmetry; apply idext_src_collapse.
    + rewrite (m_comp_left n (interp y) (interp x)).
      2: apply interp_canonical.
      2: apply interp_canonical.
      2:{ rewrite Hny, Hc. exact HB. }
      rewrite (m_comp_left n (m_tgt (interp y)) (m_tgt (interp x))).
      * reflexivity.
      * apply m_tgt_canonical; apply interp_canonical.
      * apply m_tgt_canonical; apply interp_canonical.
      * rewrite ndim_m_tgt by (rewrite Hny; lia). rewrite Hny.
        replace (d - 1 - n) with (S c'') by lia.
        rewrite HB, m_tgt_idext_tgt_S. reflexivity.
  - (* IC9 assoc *) intros x y z n d Hwf1 IH1 Hwf2 IH2.
    apply wf_comp_inv in Hwf1. destruct Hwf1 as (Hxy & Hz & Hk & _).
    apply wf_comp_inv in Hxy. destruct Hxy as (Hx & Hy & _ & _).
    pose proof (interp_ndim _ _ Hx) as HnX.
    pose proof (interp_ndim _ _ Hy) as HnY.
    destruct IH1 as (OL & IH1xy & QZ). destruct IH1xy as (IL & QX & QY).
    destruct IH2 as (OR & QX2 & IH2yz). destruct IH2yz as (IR & QY2 & QZ2).
    cbn [interp].
    destruct (m_comp_boundary (d - n) (interp x) (interp y) IL) as [ILa | ILb];
    destruct (m_comp_boundary (d - n) (interp y) (interp z) IR) as [IRa | IRb].
    + rewrite (m_comp_idsrc n d (interp x) (interp y) HnX ILa).
      rewrite (m_comp_idsrc n d (interp y) (interp z) HnY IRa).
      assert (HZ : interp z = interp y) by (rewrite IRa, ILa, idext_src_idem; reflexivity).
      rewrite HZ. reflexivity.
    + rewrite (m_comp_idsrc n d (interp x) (interp y) HnX ILa).
      rewrite (m_comp_idtgt n d (interp y) (interp z) HnY
                 (interp_canonical _) (interp_canonical _) IRb).
      reflexivity.
    + rewrite (m_comp_idtgt n d (interp x) (interp y) HnX
                 (interp_canonical _) (interp_canonical _) ILb).
      rewrite (m_comp_idsrc n d (interp y) (interp z) HnY IRa).
      rewrite (m_comp_idtgt n d (interp x) (interp y) HnX
                 (interp_canonical _) (interp_canonical _) ILb).
      reflexivity.
    + rewrite (m_comp_idtgt n d (interp x) (interp y) HnX
                 (interp_canonical _) (interp_canonical _) ILb).
      rewrite (m_comp_idtgt n d (interp y) (interp z) HnY
                 (interp_canonical _) (interp_canonical _) IRb).
      assert (HX : interp x = idext_tgt (d - n) (interp z))
        by (rewrite ILb, IRb, idext_tgt_idem; reflexivity).
      rewrite (m_comp_idtgt n d (interp x) (interp z) HnX
                 (interp_canonical _) (interp_canonical _) HX).
      reflexivity.
  - (* IC10 exchange *) intros x y z w m n d Hwf1 IH1 Hwf2 IH2.
    apply wf_comp_inv in Hwf1. destruct Hwf1 as (Hxy & Hzw & Hm & _).
    apply wf_comp_inv in Hxy. destruct Hxy as (Hx & Hy & _ & _).
    apply wf_comp_inv in Hzw. destruct Hzw as (Hz & Hw & _ & _).
    pose proof (interp_ndim _ _ Hx) as HnX. pose proof (interp_ndim _ _ Hy) as HnY.
    pose proof (interp_ndim _ _ Hz) as HnZ. pose proof (interp_ndim _ _ Hw) as HnW.
    pose proof (interp_canonical x) as Cx. pose proof (interp_canonical y) as Cy.
    pose proof (interp_canonical z) as Cz. pose proof (interp_canonical w) as Cw.
    destruct IH1 as (OL & (Bxy & _ & _) & (Bzw & _ & _)).
    destruct IH2 as (OR & (Bxz & _ & _) & (Byw & _ & _)).
    cbn [interp] in OL, OR |- *.
    destruct (m_comp_boundary (d - n) _ _ Bxy) as [Exy | Exy];
    destruct (m_comp_boundary (d - n) _ _ Bzw) as [Ezw | Ezw];
    destruct (m_comp_boundary (d - m) _ _ Bxz) as [Exz | Exz];
    destruct (m_comp_boundary (d - m) _ _ Byw) as [Eyw | Eyw];
    mresH OL Exy; mresH OL Ezw; mresH OR Exz; mresH OR Eyw;
    destruct (m_comp_boundary (d - m) _ _ OL) as [EOL | EOL];
    destruct (m_comp_boundary (d - n) _ _ OR) as [EOR | EOR];
    gres.
    (* Residuals: equalities between iterated identity-extension towers.
       Express everything over a common base, then normalize towers (larger
       codim wins) after fixing the codim order. *)
    all: try reflexivity.
    all: try (destruct (le_gt_dec (d - n) (d - m));
              repeat match goal with
                | [ H : _ = idext_src _ _ |- _ ] => rewrite H in *; clear H
                | [ H : _ = idext_tgt _ _ |- _ ] => rewrite H in *; clear H
                end;
              repeat (first
                [ rewrite ab_ss by lia | rewrite ab_st by lia
                | rewrite ab_ts by lia | rewrite ab_tt by lia
                | rewrite ov_ss by lia | rewrite ov_tt by lia
                | rewrite ov_st by lia | rewrite ov_ts by lia
                | rewrite m_comp_diag ]);
              try reflexivity).
    (* Tower normalization + m_comp_diag close 59 of 64 leaves. The last 5 are
       codim-mismatch goals that hold when codims <= nl X (extensions collapse)
       and otherwise mark a contradiction branch. A guarded codim-vs-nl split
       (splitnl) collapses the small ones but the contradiction branches need a
       config-specific argument; left as the final gap. *)
    (* The 5 residual leaves are boundary-collapse cases; each matches exactly
       one of the [ic10_l1..l5] lemmas over the relevant canonical base
       ([interp x], [interp y] or [interp z]). The side-conditions ([canonical],
       [ndim _ = d], codim order) are discharged uniformly; [eapply] shelves the
       [ndim] obligations, so we also solve them after [Unshelve]. *)
    all: first
      [ eapply ic10_l1 | eapply ic10_l2 | eapply ic10_l3
      | eapply ic10_l4 | eapply ic10_l5 ].
    all: try (apply interp_canonical).
    all: try (apply interp_ndim; assumption).
    all: try lia.
    Unshelve.
    all: try (apply interp_canonical).
    all: try (apply interp_ndim; assumption).
    all: try lia.
  - (* IC11 left unit *) intros x n d Hx IHx Hd Hwf IHwf.
    rewrite interp_comp_eq. rewrite interp_idext_src.
    unfold m_comp. rewrite (interp_ndim x d Hx).
    rewrite NF_eqb_refl. reflexivity.
  - (* IC12 right unit *) intros x n d Hx IHx Hd Hwf IHwf.
    rewrite interp_comp_eq, interp_idext_tgt.
    apply wf_comp_inv in Hwf. destruct Hwf as (HL & Hxr & Hk & Hbnd).
    apply interp_ndim in HL. rewrite interp_idext_tgt in HL.
    apply m_comp_left.
    + apply idext_tgt_canonical. apply interp_canonical.
    + apply interp_canonical.
    + rewrite HL. reflexivity.
  - (* IC13 id(comp) = comp (id)(id) *) intros x y n d Hwf IHwf Hd.
    apply wf_comp_inv in Hwf. destruct Hwf as (Hy & Hx & Hk & Hbnd).
    apply Qwf_boundary in IHwf.
    pose proof (interp_ndim _ _ Hy) as Hny.
    cbn [interp]. remember (d - n) as c eqn:Hc.
    destruct (m_comp_boundary c (interp y) (interp x) IHwf) as [HA | HB].
    + rewrite (m_comp_right n (interp y) (interp x)).
      2:{ rewrite Hny, <- Hc. exact HA. }
      rewrite (m_comp_right n (m_id (interp y)) (m_id (interp x))).
      2:{ rewrite ndim_m_id, Hny. replace (S d - n) with (S c) by lia.
          rewrite HA, m_id_idext_src. reflexivity. }
      reflexivity.
    + rewrite (m_comp_left n (interp y) (interp x)).
      2: apply interp_canonical.
      2: apply interp_canonical.
      2:{ rewrite Hny, <- Hc. exact HB. }
      rewrite (m_comp_left n (m_id (interp y)) (m_id (interp x))).
      2: apply m_id_canonical; apply interp_canonical.
      2: apply m_id_canonical; apply interp_canonical.
      2:{ rewrite ndim_m_id, Hny. replace (S d - n) with (S c) by lia.
          rewrite HB, m_id_idext_tgt. reflexivity. }
      reflexivity.
  - (* wf_gen *) intros g. exact I.
  - (* wf_src *) intros e n He QHe. exact QHe.
  - (* wf_tgt *) intros e n He QHe. exact QHe.
  - (* wf_id *) intros e n He QHe. exact QHe.
  - (* wf_comp *) intros k a b n Ha QHa Hb QHb Hk Hbnd Pbnd.
    simpl. split.
    + rewrite interp_iter_src, iter_m_src_pow in Pbnd.
      rewrite interp_iter_tgt, iter_m_tgt_pow in Pbnd. exact Pbnd.
    + split; [exact QHa | exact QHb].
Qed.

(** ** The injectivity lemma (Lemma 4.2). *)
Corollary interp_sound : forall x y, x == y -> interp x = interp y.
Proof. apply interp_sound_mut. Qed.

Theorem toTerm_inj : forall u v,
  nwf u -> canonical u -> nwf v -> canonical v ->
  toTerm u == toTerm v -> u = v.
Proof.
  intros u v _ Hcu _ Hcv H.
  apply interp_sound in H.
  rewrite (interp_toTerm u Hcu) in H.
  rewrite (interp_toTerm v Hcv) in H.
  exact H.
Qed.
