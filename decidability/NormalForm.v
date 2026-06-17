(** * NormalForm.v
    Typed normal forms for EqCat∞ and a structurally-recursive normalizer.
    Reference: "Equational Reasoning in ∞-Categories", §4 (Decidability in
    the free model), Definition 4.1, Lemmas 4.2 and 4.4.

    A normal form is an expression  id^ℓ end^m a  with end ∈ {src,tgt},
    a a generator, ℓ,m ≥ 0, and (when m = 0) the two end choices identified.
    We represent these as a record [NF] in CANONICAL form: whenever the
    end-count is 0 we force the end tag to [Es], so that structural equality
    of records coincides with provable equality of the represented terms
    (this is Lemma 4.2). Every smart constructor below preserves the
    canonical-form invariant. *)

Require Import Arith PeanoNat Lia Bool.
Require Import Syntax Axioms.

Set Implicit Arguments.

(** ** End operators (src / tgt) *)
Inductive End : Type := Es | Et.

Definition End_eq_dec : forall e1 e2 : End, {e1 = e2} + {e1 <> e2}.
Proof. decide equality. Defined.

Definition end_op (e : End) : Term -> Term :=
  match e with Es => src | Et => tgt end.

Definition iter_end (e : End) (m : nat) (t : Term) : Term :=
  Nat.iter m (end_op e) t.

(** ** Normal forms as records:  id^nl end^nm a  *)
Record NF : Type := mkNF { nl : nat; ne : End; nm : nat; na : Generator }.

(** Canonical-form invariant: end-count 0 forces end tag [Es]. *)
Definition canonical (u : NF) : Prop := nm u = 0 -> ne u = Es.

(** Interpretation of a normal form as a raw term. *)
Definition toTerm (u : NF) : Term :=
  iter_id (nl u) (iter_end (ne u) (nm u) (gen (na u))).

(** Dimension of a normal form. Well-formed when [nm u <= gen_dim (na u)]. *)
Definition ndim (u : NF) : nat := nl u + (gen_dim (na u) - nm u).
Definition nwf (u : NF) : Prop := nm u <= gen_dim (na u).

(** ** Decidable / boolean equalities *)
Definition Generator_eqb (a b : Generator) : bool :=
  if Generator_eq_dec a b then true else false.
Definition End_eqb (e1 e2 : End) : bool :=
  if End_eq_dec e1 e2 then true else false.

Definition NF_eq_dec : forall u v : NF, {u = v} + {u <> v}.
Proof.
  decide equality.
  - apply Generator_eq_dec.
  - apply Nat.eq_dec.
  - apply End_eq_dec.
  - apply Nat.eq_dec.
Defined.

(** Lemma 4.2 as a boolean test on (canonical) normal forms. *)
Definition NF_eqb (u v : NF) : bool :=
  (nl u =? nl v) && (nm u =? nm v) && Generator_eqb (na u) (na v)
  && (match nm u with 0 => true | _ => End_eqb (ne u) (ne v) end).

(** ** Smart constructors implementing the rewrite rules R1–R11 *)

(** src of a normal form (R6 strips an id; otherwise src wins via R8/def). *)
Definition nf_src (u : NF) : option NF :=
  match nl u with
  | S l' => Some (mkNF l' (ne u) (nm u) (na u))
  | 0    => if nm u <? gen_dim (na u)
            then Some (mkNF 0 Es (S (nm u)) (na u))
            else None
  end.

(** tgt of a normal form (R7 strips an id; otherwise tgt wins via R9/def). *)
Definition nf_tgt (u : NF) : option NF :=
  match nl u with
  | S l' => Some (mkNF l' (ne u) (nm u) (na u))
  | 0    => if nm u <? gen_dim (na u)
            then Some (mkNF 0 Et (S (nm u)) (na u))
            else None
  end.

(** id of a normal form (always defined). *)
Definition nf_id (u : NF) : NF := mkNF (S (nl u)) (ne u) (nm u) (na u).

(** [src^c] / [tgt^c] of a normal form, as a normal form.
    Stripping an id costs one (IC3/IC4); once the [nl] ids are gone, further
    src/tgt build a fresh src- (resp. tgt-) block (R8/R9: src/tgt "wins"). *)
Definition src_pow (c : nat) (u : NF) : NF :=
  if c <=? nl u then mkNF (nl u - c) (ne u) (nm u) (na u)
  else mkNF 0 Es (nm u + (c - nl u)) (na u).
Definition tgt_pow (c : nat) (u : NF) : NF :=
  if c <=? nl u then mkNF (nl u - c) (ne u) (nm u) (na u)
  else mkNF 0 Et (nm u + (c - nl u)) (na u).

(** [id^c (src^c u)] and [id^c (tgt^c u)] : the right/left identity-extensions
    that appear in the unit laws IC11 / IC12. *)
Definition idext_src (c : nat) (u : NF) : NF :=
  let s := src_pow c u in mkNF (nl s + c) (ne s) (nm s) (na s).
Definition idext_tgt (c : nat) (u : NF) : NF :=
  let s := tgt_pow c u in mkNF (nl s + c) (ne s) (nm s) (na s).

(** Composition of two normal forms at gluing dimension [k] (Lemma 4.4).
    [n] is the common dimension, [c = n - k] the codimension. In the FREE
    model a composite of two normal forms is always degenerate: either the
    right operand is the identity-extension of [src^c] of the left (IC11,
    right unit; result = left), or the left operand is the identity-extension
    of [tgt^c] of the right (IC12, left unit; result = right). *)
Definition nf_comp (k : nat) (u v : NF) : option NF :=
  let n := ndim u in
  if negb (ndim v =? n) then None
  else if negb (k <? n) then None
  else
    let c := n - k in
    if NF_eqb v (idext_src c u) then Some u        (* right unit IC11 *)
    else if NF_eqb u (idext_tgt c v) then Some v    (* left  unit IC12 *)
    else None.

(** ** The structural normalizer *)
Fixpoint normalize (t : Term) : option NF :=
  match t with
  | gen a      => Some (mkNF 0 Es 0 a)
  | src e      => match normalize e with Some u => nf_src u | None => None end
  | tgt e      => match normalize e with Some u => nf_tgt u | None => None end
  | id  e      => match normalize e with Some u => Some (nf_id u) | None => None end
  | comp k a b => match normalize a, normalize b with
                  | Some u, Some v => nf_comp k u v
                  | _, _ => None
                  end
  end.

(** ** Definitional unfoldings of [normalize] (for clean rewriting). *)
Lemma normalize_gen_eq : forall a, normalize (gen a) = Some (mkNF 0 Es 0 a).
Proof. reflexivity. Qed.
Lemma normalize_src_eq : forall e,
  normalize (src e) = match normalize e with Some u => nf_src u | None => None end.
Proof. reflexivity. Qed.
Lemma normalize_tgt_eq : forall e,
  normalize (tgt e) = match normalize e with Some u => nf_tgt u | None => None end.
Proof. reflexivity. Qed.
Lemma normalize_id_eq : forall e,
  normalize (id e) = match normalize e with Some u => Some (nf_id u) | None => None end.
Proof. reflexivity. Qed.
Lemma normalize_comp_eq : forall k a b,
  normalize (comp k a b)
  = match normalize a, normalize b with
    | Some u, Some v => nf_comp k u v | _, _ => None end.
Proof. reflexivity. Qed.

(** ** Iteration unfolding *)
Lemma iter_end_S : forall e m t,
  iter_end e (S m) t = end_op e (iter_end e m t).
Proof. reflexivity. Qed.

Lemma iter_id_S : forall l t, iter_id (S l) t = id (iter_id l t).
Proof. reflexivity. Qed.

Lemma iter_id_0 : forall t, iter_id 0 t = t.
Proof. reflexivity. Qed.

(** ** Well-formedness of normal forms as raw terms *)

Lemma wf_iter_end : forall e m a, m <= gen_dim a ->
  wf (iter_end e m (gen a)) (gen_dim a - m).
Proof.
  intros e m a Hm. induction m as [|m' IH].
  - rewrite Nat.sub_0_r. apply wf_gen.
  - rewrite iter_end_S.
    assert (Hm' : m' <= gen_dim a) by lia.
    specialize (IH Hm').
    replace (gen_dim a - m') with (S (gen_dim a - S m')) in IH by lia.
    destruct e; simpl end_op.
    + apply (wf_src _ _ IH).
    + apply (wf_tgt _ _ IH).
Qed.

Lemma wf_iter_id : forall l X dx, wf X dx -> wf (iter_id l X) (dx + l).
Proof.
  intros l X dx H. induction l as [|l' IH].
  - rewrite Nat.add_0_r, iter_id_0. exact H.
  - rewrite iter_id_S. replace (dx + S l') with (S (dx + l')) by lia.
    apply (wf_id _ _ IH).
Qed.

Lemma toTerm_wf : forall u, nwf u -> wf (toTerm u) (ndim u).
Proof.
  intros u Hu. unfold toTerm, ndim.
  replace (nl u + (gen_dim (na u) - nm u))
    with ((gen_dim (na u) - nm u) + nl u) by lia.
  apply wf_iter_id. apply wf_iter_end. exact Hu.
Qed.

(** ** Collapse lemmas: an outer src (resp. tgt) absorbs the end-block.
    These realize rewrite rules R8/R9 (driven by IC1/IC2) plus the
    definitional [src src = src src] case. *)

Lemma src_tgt_to_src : forall a m, m < gen_dim a ->
  src (iter_end Et m (gen a)) == src (iter_end Es m (gen a)).
Proof.
  intros a m. induction m as [|m' IH]; intros Hm.
  - apply E1_refl.
  - rewrite !iter_end_S; simpl end_op.
    set (T' := iter_end Et m' (gen a)).
    set (S' := iter_end Es m' (gen a)).
    assert (HT' : wf T' (gen_dim a - m')) by (unfold T'; apply wf_iter_end; lia).
    assert (HS' : wf S' (gen_dim a - m')) by (unfold S'; apply wf_iter_end; lia).
    apply (E3_trans (src (tgt T')) (src (src T')) (src (src S'))).
    + apply E2_sym. apply (IC1 T' (gen_dim a - m')); [exact HT' | lia].
    + assert (HsT : wf (src T') (gen_dim a - S m')).
      { apply (wf_src T' (gen_dim a - S m')).
        replace (S (gen_dim a - S m')) with (gen_dim a - m') by lia. exact HT'. }
      assert (HsS : wf (src S') (gen_dim a - S m')).
      { apply (wf_src S' (gen_dim a - S m')).
        replace (S (gen_dim a - S m')) with (gen_dim a - m') by lia. exact HS'. }
      apply (E5_src (src T') (src S') (gen_dim a - S m' - 1)).
      * apply IH; lia.
      * replace (S (gen_dim a - S m' - 1)) with (gen_dim a - S m') by lia. exact HsT.
      * replace (S (gen_dim a - S m' - 1)) with (gen_dim a - S m') by lia. exact HsS.
Qed.

Lemma tgt_src_to_tgt : forall a m, m < gen_dim a ->
  tgt (iter_end Es m (gen a)) == tgt (iter_end Et m (gen a)).
Proof.
  intros a m. induction m as [|m' IH]; intros Hm.
  - apply E1_refl.
  - rewrite !iter_end_S; simpl end_op.
    set (T' := iter_end Et m' (gen a)).
    set (S' := iter_end Es m' (gen a)).
    assert (HT' : wf T' (gen_dim a - m')) by (unfold T'; apply wf_iter_end; lia).
    assert (HS' : wf S' (gen_dim a - m')) by (unfold S'; apply wf_iter_end; lia).
    apply (E3_trans (tgt (src S')) (tgt (tgt S')) (tgt (tgt T'))).
    + apply (IC2 S' (gen_dim a - m')); [exact HS' | lia].
    + assert (HtT : wf (tgt T') (gen_dim a - S m')).
      { apply (wf_tgt T' (gen_dim a - S m')).
        replace (S (gen_dim a - S m')) with (gen_dim a - m') by lia. exact HT'. }
      assert (HtS : wf (tgt S') (gen_dim a - S m')).
      { apply (wf_tgt S' (gen_dim a - S m')).
        replace (S (gen_dim a - S m')) with (gen_dim a - m') by lia. exact HS'. }
      apply (E6_tgt (tgt S') (tgt T') (gen_dim a - S m' - 1)).
      * apply IH; lia.
      * replace (S (gen_dim a - S m' - 1)) with (gen_dim a - S m') by lia. exact HtS.
      * replace (S (gen_dim a - S m' - 1)) with (gen_dim a - S m') by lia. exact HtT.
Qed.

Lemma src_end_collapse : forall a m e, m < gen_dim a ->
  src (iter_end e m (gen a)) == iter_end Es (S m) (gen a).
Proof.
  intros a m e Hm. rewrite iter_end_S; simpl end_op.
  destruct e.
  - apply E1_refl.
  - apply src_tgt_to_src; exact Hm.
Qed.

Lemma tgt_end_collapse : forall a m e, m < gen_dim a ->
  tgt (iter_end e m (gen a)) == iter_end Et (S m) (gen a).
Proof.
  intros a m e Hm. rewrite iter_end_S; simpl end_op.
  destruct e.
  - apply tgt_src_to_tgt; exact Hm.
  - apply E1_refl.
Qed.

(** ** Soundness of the unary smart constructors *)

Lemma nf_id_spec : forall u, nwf u ->
  nwf (nf_id u) /\ ndim (nf_id u) = S (ndim u) /\ toTerm (nf_id u) == id (toTerm u).
Proof.
  intros u Hu.
  assert (Hn : nwf (nf_id u))
    by (unfold nwf, nf_id; cbn [nl ne nm na]; exact Hu).
  assert (Hd : ndim (nf_id u) = S (ndim u))
    by (unfold ndim, nf_id; cbn [nl ne nm na]; lia).
  assert (Ht : toTerm (nf_id u) == id (toTerm u))
    by (unfold toTerm, nf_id; cbn [nl ne nm na]; rewrite iter_id_S; apply E1_refl).
  repeat split; assumption.
Qed.

Lemma nf_src_spec : forall u, nwf u -> ndim u > 0 ->
  exists w, nf_src u = Some w /\ nwf w /\ ndim w = ndim u - 1
            /\ toTerm w == src (toTerm u).
Proof.
  intros u Hu Hd. destruct (nl u) as [|l'] eqn:El.
  - (* nl u = 0 : create / extend a src-block (R8 / def) *)
    assert (Hlt : nm u < gen_dim (na u))
      by (unfold ndim in Hd; rewrite El in Hd; cbn in Hd; lia).
    apply Nat.ltb_lt in Hlt as Hltb.
    set (w := mkNF 0 Es (S (nm u)) (na u)).
    assert (Hs : nf_src u = Some w)
      by (unfold nf_src, w; rewrite El, Hltb; reflexivity).
    assert (Hn : nwf w) by (unfold nwf, w; cbn [nl ne nm na]; lia).
    assert (Hd2 : ndim w = ndim u - 1)
      by (unfold ndim, w; cbn [nl ne nm na]; rewrite El; cbn; lia).
    assert (Ht : toTerm w == src (toTerm u)).
    { unfold toTerm, w; cbn [nl ne nm na]; rewrite El; cbn [iter_id].
      apply E2_sym. apply src_end_collapse; exact Hlt. }
    exists w; repeat split; assumption.
  - (* nl u = S l' : strip an id (R6 / IC3) *)
    set (w := mkNF l' (ne u) (nm u) (na u)).
    assert (Hs : nf_src u = Some w)
      by (unfold nf_src, w; rewrite El; reflexivity).
    assert (Hn : nwf w) by (unfold nwf, w; cbn [nl ne nm na]; exact Hu).
    assert (Hd2 : ndim w = ndim u - 1)
      by (unfold ndim, w; cbn [nl ne nm na]; rewrite El; cbn; lia).
    assert (Ht : toTerm w == src (toTerm u)).
    { assert (Htu : toTerm u = id (toTerm w))
        by (unfold toTerm, w; cbn [nl ne nm na]; rewrite El, iter_id_S; reflexivity).
      rewrite Htu. apply E2_sym. apply (IC3 (toTerm w) (ndim w)).
      apply toTerm_wf; exact Hn. }
    exists w; repeat split; assumption.
Qed.

Lemma nf_tgt_spec : forall u, nwf u -> ndim u > 0 ->
  exists w, nf_tgt u = Some w /\ nwf w /\ ndim w = ndim u - 1
            /\ toTerm w == tgt (toTerm u).
Proof.
  intros u Hu Hd. destruct (nl u) as [|l'] eqn:El.
  - assert (Hlt : nm u < gen_dim (na u))
      by (unfold ndim in Hd; rewrite El in Hd; cbn in Hd; lia).
    apply Nat.ltb_lt in Hlt as Hltb.
    set (w := mkNF 0 Et (S (nm u)) (na u)).
    assert (Hs : nf_tgt u = Some w)
      by (unfold nf_tgt, w; rewrite El, Hltb; reflexivity).
    assert (Hn : nwf w) by (unfold nwf, w; cbn [nl ne nm na]; lia).
    assert (Hd2 : ndim w = ndim u - 1)
      by (unfold ndim, w; cbn [nl ne nm na]; rewrite El; cbn; lia).
    assert (Ht : toTerm w == tgt (toTerm u)).
    { unfold toTerm, w; cbn [nl ne nm na]; rewrite El; cbn [iter_id].
      apply E2_sym. apply tgt_end_collapse; exact Hlt. }
    exists w; repeat split; assumption.
  - set (w := mkNF l' (ne u) (nm u) (na u)).
    assert (Hs : nf_tgt u = Some w)
      by (unfold nf_tgt, w; rewrite El; reflexivity).
    assert (Hn : nwf w) by (unfold nwf, w; cbn [nl ne nm na]; exact Hu).
    assert (Hd2 : ndim w = ndim u - 1)
      by (unfold ndim, w; cbn [nl ne nm na]; rewrite El; cbn; lia).
    assert (Ht : toTerm w == tgt (toTerm u)).
    { assert (Htu : toTerm u = id (toTerm w))
        by (unfold toTerm, w; cbn [nl ne nm na]; rewrite El, iter_id_S; reflexivity).
      rewrite Htu. apply E2_sym. apply (IC4 (toTerm w) (ndim w)).
      apply toTerm_wf; exact Hn. }
    exists w; repeat split; assumption.
Qed.

(** ** Retraction:  normalize ∘ toTerm = Some  on canonical, well-formed NFs.

    This is a purely computational correctness check on the normalizer: every
    normal form round-trips. Combined with completeness it yields injectivity
    of [toTerm] (Lemma 4.2). *)

Lemma normalize_end_pos : forall a e m, S m <= gen_dim a ->
  normalize (iter_end e (S m) (gen a)) = Some (mkNF 0 e (S m) a).
Proof.
  intros a e m. revert e. induction m as [|m' IH]; intros e Hm.
  - rewrite iter_end_S. change (iter_end e 0 (gen a)) with (gen a).
    assert (Hb : 0 <? gen_dim a = true) by (apply Nat.ltb_lt; lia).
    destruct e; cbn [end_op].
    + rewrite normalize_src_eq, normalize_gen_eq.
      unfold nf_src; cbn [nl nm na ne]; rewrite Hb; reflexivity.
    + rewrite normalize_tgt_eq, normalize_gen_eq.
      unfold nf_tgt; cbn [nl nm na ne]; rewrite Hb; reflexivity.
  - rewrite iter_end_S.
    assert (Hb : S m' <? gen_dim a = true) by (apply Nat.ltb_lt; lia).
    destruct e; cbn [end_op].
    + rewrite normalize_src_eq, (IH Es ltac:(lia)).
      unfold nf_src; cbn [nl nm na ne]; rewrite Hb; reflexivity.
    + rewrite normalize_tgt_eq, (IH Et ltac:(lia)).
      unfold nf_tgt; cbn [nl nm na ne]; rewrite Hb; reflexivity.
Qed.

Lemma normalize_iter_end : forall a e m, m <= gen_dim a -> (m = 0 -> e = Es) ->
  normalize (iter_end e m (gen a)) = Some (mkNF 0 e m a).
Proof.
  intros a e m Hm Hcanon. destruct m as [|m'].
  - rewrite (Hcanon eq_refl). reflexivity.
  - apply normalize_end_pos; lia.
Qed.

Lemma normalize_iter_id : forall l t w,
  normalize t = Some w ->
  normalize (iter_id l t) = Some (mkNF (nl w + l) (ne w) (nm w) (na w)).
Proof.
  intros l. induction l as [|l' IH]; intros t w Ht.
  - rewrite iter_id_0, Nat.add_0_r, Ht. destruct w; reflexivity.
  - rewrite iter_id_S, normalize_id_eq, (IH t w Ht).
    unfold nf_id; cbn [nl ne nm na].
    replace (nl w + S l') with (S (nl w + l')) by lia. reflexivity.
Qed.

Lemma normalize_toTerm : forall u, nwf u -> canonical u ->
  normalize (toTerm u) = Some u.
Proof.
  intros u Hu Hc. unfold toTerm.
  pose proof (normalize_iter_end Hu Hc) as He.
  rewrite (@normalize_iter_id (nl u) (iter_end (ne u) (nm u) (gen (na u)))
                              (mkNF 0 (ne u) (nm u) (na u)) He).
  cbn [nl ne nm na]. destruct u; reflexivity.
Qed.
