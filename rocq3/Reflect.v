(** * Reflect.v
    Proof by reflection: the decision procedure of [Decidable.v] packaged
    as tactics that close concrete goals by computation.

    The blurb this artifact answers:

      "boundary matching, repeated source and target simplification,
       identity propagation, and equality of closed terms in the free
       setting ... reduce to comparison of normal forms."

    Three boolean checkers, each with a soundness theorem:

      - [wfb t = Some d]        -> [wf t d]          (boundary matching)
      - [check_eq t1 t2 = true] -> [t1 == t2]        (equality)
      - [check_neq t1 t2 = true]-> [~ t1 == t2]      (refutation)

    and three tactics [eqcat_wf], [eqcat_decide], [eqcat_refute] that
    apply the soundness theorem and discharge the boolean premise by
    [vm_compute; reflexivity]. On concrete generators (a module
    implementing [GEN] with computable [gen_dim] and [Generator_eq_dec])
    this makes every obligation named above a one-word proof. *)

Require Import Arith PeanoNat Lia Bool.
Require Import Syntax Axioms Meta NormalForm Model FreeModel Decidable.

Module ReflectF (G : GEN).
Include DecidableF G.

(** ** A boolean well-formedness checker.
    Mirrors [dim], except that on [comp k a b] it also checks the boundary
    condition  src^{n-k} a == tgt^{n-k} b  by normalizing both sides and
    comparing normal forms. This is exactly the "boundary matching"
    obligation, discharged by the normalizer. *)
Fixpoint wfb (t : Term) : option nat :=
  match t with
  | gen g    => Some (gen_dim g)
  | src e    => match wfb e with Some (S n) => Some n | _ => None end
  | tgt e    => match wfb e with Some (S n) => Some n | _ => None end
  | id  e    => match wfb e with Some n => Some (S n) | None => None end
  | comp k a b =>
      match wfb a, wfb b with
      | Some da, Some db =>
          if (da =? db) && (k <? da) then
            match normalize (iter_src (da - k) a),
                  normalize (iter_tgt (da - k) b) with
            | Some u, Some v => if NF_eq_dec u v then Some da else None
            | _, _ => None
            end
          else None
      | _, _ => None
      end
  end.

(** Boundary discharge: equal normal forms of the two boundaries give the
    boundary equation of [wf_comp]. *)
Lemma boundary_by_normalize : forall c a b n,
  wf a n -> wf b n -> c <= n ->
  normalize (iter_src c a) = normalize (iter_tgt c b) ->
  iter_src c a == iter_tgt c b.
Proof.
  intros c a b n Ha Hb Hc Hn.
  assert (Hsa : wf (iter_src c a) (n - c)) by (apply wf_iter_src; assumption).
  assert (Htb : wf (iter_tgt c b) (n - c)) by (apply wf_iter_tgt; assumption).
  destruct (normalize_total Hsa) as (u & Hu & _ & _ & _ & Hsu).
  destruct (normalize_total Htb) as (v & Hv & _ & _ & _ & Hsv).
  rewrite Hu, Hv in Hn. injection Hn as <-.
  apply (E3_trans _ (toTerm u) _).
  - apply E2_sym; exact Hsu.
  - exact Hsv.
Qed.

Theorem wfb_sound : forall t d, wfb t = Some d -> wf t d.
Proof.
  induction t as [g | e IH | e IH | e IH | k a IHa b IHb]; intros d H; simpl in H.
  - injection H as <-. apply wf_gen.
  - destruct (wfb e) as [[|n]|] eqn:He; try discriminate.
    injection H as <-. apply wf_src. apply IH. reflexivity.
  - destruct (wfb e) as [[|n]|] eqn:He; try discriminate.
    injection H as <-. apply wf_tgt. apply IH. reflexivity.
  - destruct (wfb e) as [n|] eqn:He; try discriminate.
    injection H as <-. apply wf_id. apply IH. reflexivity.
  - destruct (wfb a) as [da|] eqn:Ha; try discriminate.
    destruct (wfb b) as [db|] eqn:Hb; try discriminate.
    destruct ((da =? db) && (k <? da)) eqn:Hg; try discriminate.
    apply andb_true_iff in Hg as [Hdd Hk].
    apply Nat.eqb_eq in Hdd. apply Nat.ltb_lt in Hk. subst db.
    destruct (normalize (iter_src (da - k) a)) as [u|] eqn:Hu; try discriminate.
    destruct (normalize (iter_tgt (da - k) b)) as [v|] eqn:Hv; try discriminate.
    destruct (NF_eq_dec u v) as [<- | _]; try discriminate.
    injection H as <-.
    apply wf_comp; [apply IHa; reflexivity | apply IHb; reflexivity | exact Hk |].
    apply (boundary_by_normalize (da - k) a b da);
      [apply IHa; reflexivity | apply IHb; reflexivity | lia |].
    rewrite Hu, Hv. reflexivity.
Qed.

(** ** Equality of closed terms, as a boolean. *)
Definition check_eq (t1 t2 : Term) : bool :=
  match wfb t1, wfb t2, normalize t1, normalize t2 with
  | Some _, Some _, Some u, Some v => if NF_eq_dec u v then true else false
  | _, _, _, _ => false
  end.

Theorem check_eq_sound : forall t1 t2, check_eq t1 t2 = true -> t1 == t2.
Proof.
  intros t1 t2 H. unfold check_eq in H.
  destruct (wfb t1) as [d1|] eqn:H1; try discriminate.
  destruct (wfb t2) as [d2|] eqn:H2; try discriminate.
  destruct (normalize t1) as [u|] eqn:Hu; try discriminate.
  destruct (normalize t2) as [v|] eqn:Hv; try discriminate.
  destruct (NF_eq_dec u v) as [<- | _]; try discriminate.
  apply wfb_sound in H1. apply wfb_sound in H2.
  apply (E3_trans _ (toTerm u) _).
  - apply E2_sym. exact (normalize_sound H1 Hu).
  - exact (normalize_sound H2 Hv).
Qed.

(** ** Refutation: both sides well-formed, normal forms differ. *)
Definition check_neq (t1 t2 : Term) : bool :=
  match wfb t1, wfb t2, normalize t1, normalize t2 with
  | Some _, Some _, Some u, Some v => if NF_eq_dec u v then false else true
  | _, _, _, _ => false
  end.

Theorem check_neq_sound : forall t1 t2, check_neq t1 t2 = true -> ~ t1 == t2.
Proof.
  intros t1 t2 H Heq. unfold check_neq in H.
  destruct (wfb t1) as [d1|] eqn:H1; try discriminate.
  destruct (wfb t2) as [d2|] eqn:H2; try discriminate.
  destruct (normalize t1) as [u|] eqn:Hu; try discriminate.
  destruct (normalize t2) as [v|] eqn:Hv; try discriminate.
  destruct (NF_eq_dec u v) as [_ | N]; try discriminate.
  apply wfb_sound in H1. apply wfb_sound in H2.
  pose proof (normalize_complete H1 H2 Heq) as Hn.
  rewrite Hu, Hv in Hn. injection Hn as Hn. exact (N Hn).
Qed.

(** Completeness of the boolean checker relative to the theory: on
    well-formed terms, provable equality is detected. So [eqcat_decide]
    never fails on a true equation between well-formed closed terms. *)
Lemma wfb_complete : forall t d, wf t d -> wfb t = Some d.
Proof.
  intros t d H. induction H as [g | e n He IH | e n He IH | e n He IH
                                | k a b n Ha IHa Hb IHb Hk Hbnd].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - simpl. rewrite IHa, IHb, Nat.eqb_refl.
    assert (Hkb : (k <? n) = true) by (apply Nat.ltb_lt; exact Hk).
    rewrite Hkb. simpl.
    assert (Hsa : wf (iter_src (n - k) a) (n - (n - k)))
      by (apply wf_iter_src; [exact Ha | lia]).
    assert (Htb : wf (iter_tgt (n - k) b) (n - (n - k)))
      by (apply wf_iter_tgt; [exact Hb | lia]).
    pose proof (normalize_complete Hsa Htb Hbnd) as Hn.
    destruct (normalize_total Hsa) as (u & Hu & _).
    rewrite Hu in Hn |- *. rewrite <- Hn.
    destruct (NF_eq_dec u u) as [_ | N]; [reflexivity | contradiction].
Qed.

Theorem check_eq_complete : forall t1 t2 d1 d2,
  wf t1 d1 -> wf t2 d2 -> t1 == t2 -> check_eq t1 t2 = true.
Proof.
  intros t1 t2 d1 d2 H1 H2 Heq. unfold check_eq.
  rewrite (wfb_complete _ _ H1), (wfb_complete _ _ H2).
  pose proof (normalize_complete H1 H2 Heq) as Hn.
  destruct (normalize_total H1) as (u & Hu & _).
  rewrite Hu in Hn |- *. rewrite <- Hn.
  destruct (NF_eq_dec u u) as [_ | N]; [reflexivity | contradiction].
Qed.

(** ** The tactics.
    Each one applies a soundness theorem and then runs the checker. On a
    concrete instantiation of [GEN] the checker reduces to a literal
    boolean under [vm_compute], and [reflexivity] closes it. *)

(** Close a goal [wf t d]. *)
Ltac eqcat_wf := apply wfb_sound; vm_compute; reflexivity.

(** Close a goal [t1 == t2], or [c1 === c2] on [FreeCell]s. *)
Ltac eqcat_decide :=
  try (unfold FreeCell_eq; cbn [cell_term]);
  apply check_eq_sound; vm_compute; reflexivity.

(** Close a goal [~ t1 == t2]. *)
Ltac eqcat_refute :=
  try (unfold FreeCell_eq; cbn [cell_term]);
  apply check_neq_sound; vm_compute; reflexivity.

(** Build a [FreeCell] from a closed term, discharging [wf] by computation. *)
Ltac mkcell t d :=
  let t' := constr:(t) in let d' := constr:(d) in
  exact {| cell_term := t'; cell_dim := d'; cell_proof := ltac:(eqcat_wf) |}.

End ReflectF.
