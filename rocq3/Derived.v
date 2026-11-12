(** * Derived.v
    Facts stated in Section 2 of the paper as consequences of the axioms,
    proved here from the rules of [Axioms.v] for arbitrary well-formed terms
    (no use of the normalizer):

      - [word_collapse]: a word of [src]/[tgt] applied to a term is
        determined by its outermost letter and its length.
      - [comp_iter_src], [comp_iter_tgt]: the iterated boundary of a
        composite, src^c (b ∘_k a) == src^c a and tgt^c (b ∘_k a) == tgt^c b
        where c is the codimension of the gluing cell.
      - [typing_rule_1], [typing_rule_2]: the two typing rules for
        composition.

    The last section restates Lemma 4.4 of the paper (composition of two
    normal forms) in the paper's own parameters, with the results of
    cases (b) and (c) corrected. That part does use the normalizer.

    Convention as in [Axioms.v]: [comp k b a] is b ∘_k a, well-formed at
    dimension n when src^{n-k} b == tgt^{n-k} a. The paper writes this
    composite as b ∘_{n-c} a with c = n - k the codimension. *)

Require Import Arith PeanoNat Lia Bool List.
Require Import Syntax Axioms Meta NormalForm Model FreeModel Decidable Reflect.
Import ListNotations.

Module DerivedF (G : GEN).
Include ReflectF G.

(** ** 1. Words of src and tgt *)

(** [apply_word [e1; ...; en] x] is e1 (e2 (... (en x))): the head of the
    list is the outermost operator, i.e. the one the word "begins with". *)
Fixpoint apply_word (w : list End) (x : Term) : Term :=
  match w with
  | []      => x
  | e :: w' => end_op e (apply_word w' x)
  end.

Lemma wf_apply_word : forall w x d,
  wf x d -> length w <= d -> wf (apply_word w x) (d - length w).
Proof.
  induction w as [|e w IH]; intros x d Hx Hl; simpl in *.
  - rewrite Nat.sub_0_r. exact Hx.
  - assert (H : wf (apply_word w x) (S (d - S (length w)))).
    { replace (S (d - S (length w))) with (d - length w) by lia.
      apply IH; [exact Hx | lia]. }
    destruct e; simpl; [apply wf_src | apply wf_tgt]; exact H.
Qed.

(** One more [src] (resp. [tgt]) on top of any word gives the pure iterate.
    Uses only globularity (IC1, IC2) and congruence (E5, E6). *)
Lemma word_collapse : forall w x d,
  wf x d -> S (length w) <= d ->
  src (apply_word w x) == iter_src (S (length w)) x /\
  tgt (apply_word w x) == iter_tgt (S (length w)) x.
Proof.
  induction w as [|e w IH]; intros x d Hx Hl.
  - split; apply E1_refl.
  - simpl length in *.
    destruct (IH x d Hx ltac:(lia)) as [IHs IHt].
    set (y := apply_word w x) in *.
    assert (Hy : wf y (d - length w)) by (apply wf_apply_word; [exact Hx | lia]).
    assert (Hsy : wf (src y) (S (d - S (S (length w))))).
    { apply wf_src. replace (S (S (d - S (S (length w))))) with (d - length w) by lia. exact Hy. }
    assert (Hty : wf (tgt y) (S (d - S (S (length w))))).
    { apply wf_tgt. replace (S (S (d - S (S (length w))))) with (d - length w) by lia. exact Hy. }
    assert (His : wf (iter_src (S (length w)) x) (S (d - S (S (length w))))).
    { replace (S (d - S (S (length w)))) with (d - S (length w)) by lia.
      apply wf_iter_src; [exact Hx | lia]. }
    assert (Hit : wf (iter_tgt (S (length w)) x) (S (d - S (S (length w))))).
    { replace (S (d - S (S (length w)))) with (d - S (length w)) by lia.
      apply wf_iter_tgt; [exact Hx | lia]. }
    assert (Hss : src (src y) == iter_src (S (S (length w))) x).
    { change (iter_src (S (S (length w))) x) with (src (iter_src (S (length w)) x)).
      apply (E5_src _ _ (d - S (S (length w)))); assumption. }
    assert (Htt : tgt (tgt y) == iter_tgt (S (S (length w))) x).
    { change (iter_tgt (S (S (length w))) x) with (tgt (iter_tgt (S (length w)) x)).
      apply (E6_tgt _ _ (d - S (S (length w)))); assumption. }
    change (apply_word (e :: w) x) with (end_op e y).
    destruct e; simpl end_op; split.
    + exact Hss.
    + apply (E3_trans _ (tgt (tgt y)) _); [| exact Htt].
      apply (IC2 y (d - length w)); [exact Hy | lia].
    + apply (E3_trans _ (src (src y)) _); [| exact Hss].
      apply E2_sym. apply (IC1 y (d - length w)); [exact Hy | lia].
    + exact Htt.
Qed.

(** The statement of Section 2.1: a word of length n beginning with [src]
    equals src^n, and one beginning with [tgt] equals tgt^n. *)
Theorem src_word : forall w x d,
  wf x d -> length (Es :: w) <= d ->
  apply_word (Es :: w) x == iter_src (length (Es :: w)) x.
Proof. intros w x d Hx Hl. exact (proj1 (word_collapse w x d Hx Hl)). Qed.

Theorem tgt_word : forall w x d,
  wf x d -> length (Et :: w) <= d ->
  apply_word (Et :: w) x == iter_tgt (length (Et :: w)) x.
Proof. intros w x d Hx Hl. exact (proj2 (word_collapse w x d Hx Hl)). Qed.

(** The paper's example: src src tgt src tgt x == src^5 x when dim x >= 5. *)
Example src_word_example : forall x d, wf x d -> 5 <= d ->
  src (src (tgt (src (tgt x)))) == src (src (src (src (src x)))).
Proof. intros x d Hx Hd. exact (src_word [Es; Et; Es; Et] x d Hx Hd). Qed.

(** ** 2. Iterated boundary of a composite *)

(** tgt^c (src a) == tgt^(c+1) a and src^c (tgt a) == src^(c+1) a for c >= 1. *)
Lemma iter_tgt_src : forall c a d,
  wf a d -> 1 <= c -> S c <= d -> iter_tgt c (src a) == iter_tgt (S c) a.
Proof.
  intros c a d Ha Hc Hd.
  pose proof (tgt_word (repeat Et (c - 1) ++ [Es]) a d Ha) as H.
  assert (L : length (Et :: repeat Et (c - 1) ++ [Es]) = S c).
  { simpl. rewrite app_length, repeat_length. simpl. lia. }
  rewrite L in H. specialize (H Hd).
  assert (E : apply_word (Et :: repeat Et (c - 1) ++ [Es]) a = iter_tgt c (src a)).
  { clear H L Hd. destruct c as [|c]; [lia|]. simpl. rewrite Nat.sub_0_r.
    change (iter_tgt (S c) (src a)) with (tgt (iter_tgt c (src a))). f_equal.
    clear Hc. induction c as [|c IH]; [reflexivity|].
    simpl. change (iter_tgt (S c) (src a)) with (tgt (iter_tgt c (src a))).
    f_equal. exact IH. }
  rewrite E in H. exact H.
Qed.

Lemma iter_src_tgt : forall c a d,
  wf a d -> 1 <= c -> S c <= d -> iter_src c (tgt a) == iter_src (S c) a.
Proof.
  intros c a d Ha Hc Hd.
  pose proof (src_word (repeat Es (c - 1) ++ [Et]) a d Ha) as H.
  assert (L : length (Es :: repeat Es (c - 1) ++ [Et]) = S c).
  { simpl. rewrite app_length, repeat_length. simpl. lia. }
  rewrite L in H. specialize (H Hd).
  assert (E : apply_word (Es :: repeat Es (c - 1) ++ [Et]) a = iter_src c (tgt a)).
  { clear H L Hd. destruct c as [|c]; [lia|]. simpl. rewrite Nat.sub_0_r.
    change (iter_src (S c) (tgt a)) with (src (iter_src c (tgt a))). f_equal.
    clear Hc. induction c as [|c IH]; [reflexivity|].
    simpl. change (iter_src (S c) (tgt a)) with (src (iter_src c (tgt a))).
    f_equal. exact IH. }
  rewrite E in H. exact H.
Qed.

(** If b ∘_k a is well-formed above dimension k+1, so are
    src b ∘_k src a and tgt b ∘_k tgt a (the right-hand sides of IC7, IC8). *)
Lemma wf_comp_src : forall k b a d,
  wf (comp k b a) (S d) -> k < d -> wf (comp k (src b) (src a)) d.
Proof.
  intros k b a d H Hk.
  destruct (wf_comp_inv k b a (S d) H) as (Hb & Ha & _ & Hbd).
  replace (S d - k) with (S (d - k)) in Hbd by lia.
  apply wf_comp; [apply wf_src; exact Hb | apply wf_src; exact Ha | exact Hk |].
  apply (E3_trans _ (iter_tgt (S (d - k)) a) _).
  - unfold iter_src in *. rewrite <- (iter_inside src (d - k) b). exact Hbd.
  - apply E2_sym. apply (iter_tgt_src (d - k) a (S d)); [exact Ha | lia | lia].
Qed.

Lemma wf_comp_tgt : forall k b a d,
  wf (comp k b a) (S d) -> k < d -> wf (comp k (tgt b) (tgt a)) d.
Proof.
  intros k b a d H Hk.
  destruct (wf_comp_inv k b a (S d) H) as (Hb & Ha & _ & Hbd).
  replace (S d - k) with (S (d - k)) in Hbd by lia.
  apply wf_comp; [apply wf_tgt; exact Hb | apply wf_tgt; exact Ha | exact Hk |].
  apply (E3_trans _ (iter_src (S (d - k)) b) _).
  - apply (iter_src_tgt (d - k) b (S d)); [exact Hb | lia | lia].
  - unfold iter_tgt in *. rewrite <- (iter_inside tgt (d - k) a). exact Hbd.
Qed.

(** src^c (b ∘_k a) == src^c a, where c = dim - k. *)
Theorem comp_iter_src : forall c k b a,
  1 <= c -> wf (comp k b a) (k + c) -> iter_src c (comp k b a) == iter_src c a.
Proof.
  induction c as [|c IH]; intros k b a Hc H; [lia|].
  destruct c as [|c].
  - replace (k + 1) with (S k) in H by lia. exact (IC5 a b k H).
  - replace (k + S (S c)) with (S (k + S c)) in H by lia.
    assert (Hlow : wf (comp k (src b) (src a)) (k + S c))
      by (apply wf_comp_src; [exact H | lia]).
    unfold iter_src.
    rewrite (iter_inside src (S c) (comp k b a)), (iter_inside src (S c) a).
    apply (E3_trans _ (iter_src (S c) (comp k (src b) (src a))) _).
    + apply (iter_src_cong (S c) _ _ (k + S c)).
      * apply (IC7 a b k (S (k + S c))); [exact H | lia].
      * apply wf_src. exact H.
      * exact Hlow.
      * lia.
    + apply IH; [lia | exact Hlow].
Qed.

(** tgt^c (b ∘_k a) == tgt^c b, where c = dim - k. *)
Theorem comp_iter_tgt : forall c k b a,
  1 <= c -> wf (comp k b a) (k + c) -> iter_tgt c (comp k b a) == iter_tgt c b.
Proof.
  induction c as [|c IH]; intros k b a Hc H; [lia|].
  destruct c as [|c].
  - replace (k + 1) with (S k) in H by lia. exact (IC6 a b k H).
  - replace (k + S (S c)) with (S (k + S c)) in H by lia.
    assert (Hlow : wf (comp k (tgt b) (tgt a)) (k + S c))
      by (apply wf_comp_tgt; [exact H | lia]).
    unfold iter_tgt.
    rewrite (iter_inside tgt (S c) (comp k b a)), (iter_inside tgt (S c) b).
    apply (E3_trans _ (iter_tgt (S c) (comp k (tgt b) (tgt a))) _).
    + apply (iter_tgt_cong (S c) _ _ (k + S c)).
      * apply (IC8 a b k (S (k + S c))); [exact H | lia].
      * apply wf_tgt. exact H.
      * exact Hlow.
      * lia.
    + apply IH; [lia | exact Hlow].
Qed.

(** ** 3. Typing rules for composition *)

(** [has_type f a b] is the judgment f : a -> b. *)
Definition has_type (f a b : Term) : Prop := src f == a /\ tgt f == b.

(** Rule (1): f : a -> b and g : b -> c give g ∘ f : a -> c, where f, g have
    dimension k+1 and the composite is along their common k-cell. The
    composite is well-formed as part of the conclusion. *)
Theorem typing_rule_1 : forall k f g a b c,
  wf f (S k) -> wf g (S k) ->
  has_type f a b -> has_type g b c ->
  wf (comp k g f) (S k) /\ has_type (comp k g f) a c.
Proof.
  intros k f g a b c Hf Hg [Hfa Hfb] [Hgb Hgc].
  assert (W : wf (comp k g f) (S k)).
  { apply wf_comp; [exact Hg | exact Hf | lia |].
    replace (S k - k) with 1 by lia.
    change (src g == tgt f).
    apply (E3_trans _ b _); [exact Hgb | apply E2_sym; exact Hfb]. }
  split; [exact W | split].
  - apply (E3_trans _ (src f) _); [exact (IC5 f g k W) | exact Hfa].
  - apply (E3_trans _ (tgt g) _); [exact (IC6 f g k W) | exact Hgc].
Qed.

(** Rule (2): alpha : f -> g and beta : h -> l, with h ∘_k f and l ∘_k g
    defined, give beta ∘_k alpha : h ∘_k f -> l ∘_k g. Here alpha, beta
    have dimension m+1 and k < m. That beta ∘_k alpha is well-formed is
    part of the conclusion. *)
Theorem typing_rule_2 : forall k m alpha beta f g h l,
  wf alpha (S m) -> wf beta (S m) -> k < m ->
  has_type alpha f g -> has_type beta h l ->
  wf (comp k h f) m -> wf (comp k l g) m ->
  wf (comp k beta alpha) (S m) /\
  has_type (comp k beta alpha) (comp k h f) (comp k l g).
Proof.
  intros k m alpha beta f g h l Ha Hb Hk [Haf Hag] [Hbh Hbl] Whf Wlg.
  destruct (wf_comp_inv k h f m Whf) as (Hh & Hf & _ & Bhf).
  assert (W : wf (comp k beta alpha) (S m)).
  { apply wf_comp; [exact Hb | exact Ha | lia |].
    replace (S m - k) with (S (m - k)) by lia.
    unfold iter_src. rewrite (iter_inside src (m - k) beta).
    change (iter_src (m - k) (src beta) == iter_tgt (S (m - k)) alpha).
    apply (E3_trans _ (iter_src (m - k) h) _).
    { apply (iter_src_cong (m - k) _ _ m);
        [exact Hbh | apply wf_src; exact Hb | exact Hh | lia]. }
    apply (E3_trans _ (iter_tgt (m - k) f) _); [exact Bhf |].
    apply (E3_trans _ (iter_tgt (m - k) (src alpha)) _).
    { apply E2_sym. apply (iter_tgt_cong (m - k) _ _ m);
        [exact Haf | apply wf_src; exact Ha | exact Hf | lia]. }
    apply (iter_tgt_src (m - k) alpha (S m)); [exact Ha | lia | lia]. }
  split; [exact W | split].
  - apply (E3_trans _ (comp k (src beta) (src alpha)) _).
    + apply (IC7 alpha beta k (S m)); [exact W | lia].
    + apply (E7_comp _ _ _ _ k m); [exact Hbh | exact Haf | | exact Whf].
      apply wf_comp_src; [exact W | exact Hk].
  - apply (E3_trans _ (comp k (tgt beta) (tgt alpha)) _).
    + apply (IC8 alpha beta k (S m)); [exact W | lia].
    + apply (E7_comp _ _ _ _ k m); [exact Hbl | exact Hag | | exact Wlg].
      apply wf_comp_tgt; [exact W | exact Hk].
Qed.

(** ** 4. Composition of two normal forms (Lemma 4.4 of the paper) *)

Lemma tgt_pow_idext_src : forall c u, tgt_pow c (idext_src c u) = src_pow c u.
Proof.
  intros c u. rewrite tgt_pow_le by (rewrite idext_src_nl; lia).
  unfold idext_src; cbn [nl ne nm na].
  replace (nl (src_pow c u) + c - c) with (nl (src_pow c u)) by lia.
  destruct (src_pow c u); reflexivity.
Qed.

Lemma src_pow_idext_tgt : forall c v, src_pow c (idext_tgt c v) = tgt_pow c v.
Proof.
  intros c v. rewrite src_pow_le by (rewrite idext_tgt_nl; lia).
  unfold idext_tgt; cbn [nl ne nm na].
  replace (nl (tgt_pow c v) + c - c) with (nl (tgt_pow c v)) by lia.
  destruct (tgt_pow c v); reflexivity.
Qed.

(** The composite u ∘_k v of two normal forms of dimension n is well-formed
    exactly when one operand is the unit for the other: v = id^c src^c u
    (then the composite is u) or u = id^c tgt^c v (then it is v), c = n - k. *)
Theorem nf_compose : forall k n u v,
  nwf u -> canonical u -> ndim u = n ->
  nwf v -> canonical v -> ndim v = n -> k < n ->
  (wf (comp k (toTerm u) (toTerm v)) n <->
     (v = idext_src (n - k) u \/ u = idext_tgt (n - k) v))
  /\ (v = idext_src (n - k) u -> comp k (toTerm u) (toTerm v) == toTerm u)
  /\ (u = idext_tgt (n - k) v -> comp k (toTerm u) (toTerm v) == toTerm v).
Proof.
  intros k n u v Hnu Hcu Hdu Hnv Hcv Hdv Hk.
  set (c := n - k).
  assert (Hc : c <= n) by (unfold c; lia).
  assert (Ha : wf (toTerm u) n) by (rewrite <- Hdu; apply toTerm_wf; exact Hnu).
  assert (Hb : wf (toTerm v) n) by (rewrite <- Hdv; apply toTerm_wf; exact Hnv).
  assert (Hsp : toTerm (src_pow c u) == iter_src c (toTerm u))
    by (apply src_pow_sound; [exact Hnu | lia]).
  assert (Htp : toTerm (tgt_pow c v) == iter_tgt c (toTerm v))
    by (apply tgt_pow_sound; [exact Hnv | lia]).
  (* A matched boundary, as an equation of normal forms, gives everything. *)
  assert (G : src_pow c u = tgt_pow c v ->
              wf (comp k (toTerm u) (toTerm v)) n /\
              exists w, nf_comp k u v = Some w /\
                        toTerm w == comp k (toTerm u) (toTerm v)).
  { intro Hglue. split.
    - apply wf_comp; [exact Ha | exact Hb | exact Hk |]. fold c.
      apply (E3_trans _ (toTerm (src_pow c u)) _); [apply E2_sym; exact Hsp |].
      rewrite Hglue. exact Htp.
    - destruct (nf_comp_glue k (toTerm u) (toTerm v) n u v Ha Hb Hk
                  (normalize_toTerm Hnu Hcu) (normalize_toTerm Hnv Hcv)
                  Hnu Hcu Hdu Hnv Hcv Hdv (E1_refl _) (E1_refl _) Hglue)
        as (w & Hw & _ & _ & _ & Hs).
      exists w. split; assumption. }
  assert (GL : v = idext_src c u -> src_pow c u = tgt_pow c v)
    by (intro E; rewrite E; symmetry; apply tgt_pow_idext_src).
  assert (GR : u = idext_tgt c v -> src_pow c u = tgt_pow c v)
    by (intro E; rewrite E; apply src_pow_idext_tgt).
  split; [split | split].
  - intro W. apply m_comp_boundary.
    destruct (wf_comp_inv k _ _ n W) as (_ & _ & _ & Hbd). fold c in Hbd.
    apply toTerm_inj.
    + apply src_pow_nwf; [exact Hnu | lia].
    + apply src_pow_canonical; exact Hcu.
    + apply tgt_pow_nwf; [exact Hnv | lia].
    + apply tgt_pow_canonical; exact Hcv.
    + apply (E3_trans _ (iter_src c (toTerm u)) _); [exact Hsp |].
      apply (E3_trans _ (iter_tgt c (toTerm v)) _); [exact Hbd | apply E2_sym; exact Htp].
  - intros [E | E]; [exact (proj1 (G (GL E))) | exact (proj1 (G (GR E)))].
  - intro E. destruct (proj2 (G (GL E))) as (w & Hw & Hs).
    unfold nf_comp in Hw. rewrite Hdu, Hdv, Nat.eqb_refl in Hw. simpl negb in Hw.
    assert (Hlt : (k <? n) = true) by (apply Nat.ltb_lt; exact Hk).
    rewrite Hlt in Hw. simpl in Hw. fold c in Hw.
    rewrite E, NF_eqb_refl in Hw. injection Hw as <-. apply E2_sym. exact Hs.
  - intro E. destruct (proj2 (G (GR E))) as (w & Hw & Hs).
    unfold nf_comp in Hw. rewrite Hdu, Hdv, Nat.eqb_refl in Hw. simpl negb in Hw.
    assert (Hlt : (k <? n) = true) by (apply Nat.ltb_lt; exact Hk).
    rewrite Hlt in Hw. simpl in Hw. fold c in Hw.
    destruct (NF_eqb v (idext_src c u)) eqn:E1.
    + apply NF_eqb_eq in E1; [| exact Hcv | apply idext_src_canonical; exact Hcu].
      rewrite E, idext_src_idext_tgt, <- E in E1.
      injection Hw as <-. rewrite E1. apply E2_sym. rewrite E1 in Hs. exact Hs.
    + rewrite E, NF_eqb_refl in Hw. injection Hw as <-. apply E2_sym. exact Hs.
Qed.

(** Lemma 4.4 in the paper's parameters. u = id^l end1^m a and
    v = id^i end2^j b have dimension n, and c = n - k is the paper's k, so
    [comp k u v] is the paper's u ∘_{n-k} v with boundary condition
    src^c u = tgt^c v. The three cases have the paper's conditions. The
    results differ from the paper's statement in (b) and (c): the composite
    is v in case (b) and u in case (c). *)
Theorem lemma_4_4 : forall k n l e1 m a i e2 j b,
  nwf (mkNF l e1 m a) -> canonical (mkNF l e1 m a) -> ndim (mkNF l e1 m a) = n ->
  nwf (mkNF i e2 j b) -> canonical (mkNF i e2 j b) -> ndim (mkNF i e2 j b) = n ->
  k < n ->
  let u := mkNF l e1 m a in
  let v := mkNF i e2 j b in
  let c := n - k in
  let case_a := c <= l /\ c <= i /\ u = v in
  let case_b := c <= l /\ i < c /\ l = c /\ e1 = Et /\ m = j + c - i in
  let case_c := l < c /\ c <= i /\ i = c /\ e2 = Es /\ j = m + c - l in
  (wf (comp k (toTerm u) (toTerm v)) n <-> a = b /\ (case_a \/ case_b \/ case_c))
  /\ (a = b /\ case_a -> comp k (toTerm u) (toTerm v) == toTerm u)
  /\ (a = b /\ case_b -> comp k (toTerm u) (toTerm v) == toTerm v)
  /\ (a = b /\ case_c -> comp k (toTerm u) (toTerm v) == toTerm u)
  /\ (l < c -> i < c -> ~ wf (comp k (toTerm u) (toTerm v)) n).
Proof.
  intros k n l e1 m a i e2 j b Hnu Hcu Hdu Hnv Hcv Hdv Hk u v c case_a case_b case_c.
  destruct (nf_compose k n u v Hnu Hcu Hdu Hnv Hcv Hdv Hk) as (Hiff & HL & HR).
  fold c in Hiff, HL, HR.
  assert (A1 : a = b /\ case_a -> v = idext_src c u).
  { intros (_ & Hl & _ & E). rewrite (idext_src_le c u) by exact Hl. symmetry; exact E. }
  assert (B1 : a = b /\ case_b -> u = idext_tgt c v).
  { intros (Eab & _ & Hi & El & Ee & Em).
    rewrite (idext_tgt_gt c v) by exact Hi. unfold u, v; cbn [nl ne nm na].
    f_equal; [exact El | exact Ee | lia | exact Eab]. }
  assert (C1 : a = b /\ case_c -> v = idext_src c u).
  { intros (Eab & Hl & _ & Ei & Ee & Ej).
    rewrite (idext_src_gt c u) by exact Hl. unfold u, v; cbn [nl ne nm na].
    f_equal; [exact Ei | exact Ee | lia | symmetry; exact Eab]. }
  assert (Dir : (v = idext_src c u \/ u = idext_tgt c v) ->
                a = b /\ (case_a \/ case_b \/ case_c)).
  { intros [E | E].
    - destruct (le_gt_dec c l) as [Hl | Hl].
      + assert (Euv : u = v)
          by (rewrite (idext_src_le c u) in E by exact Hl; symmetry; exact E).
        assert (Hinj := Euv). unfold u, v in Hinj. injection Hinj as I1 I2 I3 I4.
        split; [exact I4 |]. left. split; [exact Hl | split; [lia | exact Euv]].
      + rewrite (idext_src_gt c u) in E by exact Hl.
        unfold u, v in E; cbn [nl ne nm na] in E. injection E as I1 I2 I3 I4.
        split; [symmetry; exact I4 |]. right; right.
        split; [exact Hl | split; [lia | split; [exact I1 | split; [exact I2 | lia]]]].
    - destruct (le_gt_dec c i) as [Hi | Hi].
      + assert (Euv : u = v)
          by (rewrite (idext_tgt_le c v) in E by exact Hi; exact E).
        assert (Hinj := Euv). unfold u, v in Hinj. injection Hinj as I1 I2 I3 I4.
        split; [exact I4 |]. left. split; [lia | split; [exact Hi | exact Euv]].
      + rewrite (idext_tgt_gt c v) in E by exact Hi.
        unfold u, v in E; cbn [nl ne nm na] in E. injection E as I1 I2 I3 I4.
        split; [exact I4 |]. right; left.
        split; [lia | split; [exact Hi | split; [exact I1 | split; [exact I2 | lia]]]]. }
  split; [split |].
  - intro W. apply Dir. apply Hiff. exact W.
  - intros (Eab & [Hc | [Hc | Hc]]); apply Hiff.
    + left. apply A1. split; assumption.
    + right. apply B1. split; assumption.
    + left. apply C1. split; assumption.
  - repeat split.
    + intro H. apply HL. apply A1. exact H.
    + intro H. apply HR. apply B1. exact H.
    + intro H. apply HL. apply C1. exact H.
    + intros Hl Hi W.
      destruct (Dir (proj1 Hiff W)) as (_ & [(H1 & _) | [(H1 & _) | (_ & H1 & _)]]); lia.
Qed.

End DerivedF.

(** ** Check of [lemma_4_4] on the counterexample to the paper's case (b).
    With one 2-dimensional generator alpha, take u = id (tgt alpha) and
    v = alpha, composed along dimension 1. This is case (b), and the
    composite is v = alpha (the paper's statement gives u). *)
Module L44Gen <: GEN.
  Inductive G := alpha.
  Definition Generator := G.
  Definition gen_dim (g : G) : nat := 2.
  Definition Generator_eq_dec : forall g1 g2 : Generator, {g1 = g2} + {g1 <> g2}.
  Proof. decide equality. Defined.
End L44Gen.

Module L44 := DerivedF L44Gen.
Import L44.

Example lemma_4_4_case_b :
  comp 1 (id (tgt (gen L44Gen.alpha))) (gen L44Gen.alpha) == gen L44Gen.alpha.
Proof.
  destruct (lemma_4_4 1 2 1 Et 1 L44Gen.alpha 0 Es 0 L44Gen.alpha) as (_ & _ & HB & _).
  - cbv; lia.
  - cbv; intro H; discriminate.
  - reflexivity.
  - cbv; lia.
  - cbv; intro H; reflexivity.
  - reflexivity.
  - lia.
  - apply HB. cbv. repeat split; lia.
Qed.

Print Assumptions lemma_4_4_case_b.
Print Assumptions L44.typing_rule_2.
Print Assumptions L44.comp_iter_src.
Print Assumptions L44.src_word.
