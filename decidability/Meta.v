(** * Meta.v
    Metatheory of [wf] and [eq_cat]: well-formedness determines dimension,
    and provable equality preserves dimension.

    Main results:
      - [wf_dim_sound]   : wf t d -> dim t = Some d
      - [wf_dim_unique]  : wf t d -> wf t d' -> d = d'
      - [eq_cat_dim]     : x == y -> dim x = dim y
      - [eq_cat_dim_agree] : x == y -> wf x d1 -> wf y d2 -> d1 = d2

    The last item discharges the [Admitted] in [FreeModel.v]. *)

Require Import Arith Lia.
Require Import Syntax Axioms.

(** ** wf is sound for the syntactic [dim] *)
Lemma wf_dim_sound : forall t d, wf t d -> dim t = Some d.
Proof.
  intros t d H. induction H.
  - apply dim_gen.
  - apply dim_src; exact IHwf.
  - apply dim_tgt; exact IHwf.
  - apply dim_id; exact IHwf.
  - apply dim_comp; [exact IHwf1 | exact IHwf2 | exact H1].
Qed.

(** ** wf determines dimension uniquely *)
Lemma wf_dim_unique : forall t d d', wf t d -> wf t d' -> d = d'.
Proof.
  intros t d d' H1 H2.
  apply wf_dim_sound in H1. apply wf_dim_sound in H2.
  rewrite H1 in H2. injection H2; auto.
Qed.

(** ** Inversion for compositions *)
Lemma wf_comp_inv : forall k a b d,
  wf (comp k a b) d ->
  wf a d /\ wf b d /\ k < d /\ iter_src (d - k) a == iter_tgt (d - k) b.
Proof.
  intros k a b d H. inversion H; subst.
  repeat split; assumption.
Qed.

(** ** Provable equality preserves dimension.

    Proof by induction on the [eq_cat] derivation. Most cases extract the
    dimensions of subterms from the [wf] premises via [wf_dim_sound] and
    then compute; only E8 and transitivity use the induction hypothesis. *)
Lemma eq_cat_dim : forall x y, x == y -> dim x = dim y.
Proof.
  intros x y H. induction H.
  - (* E1 refl *) reflexivity.
  - (* E2 sym *) symmetry; exact IHeq_cat.
  - (* E3 trans *) rewrite IHeq_cat1; exact IHeq_cat2.
  - (* E5 src *)
    apply wf_dim_sound in H0. apply wf_dim_sound in H1.
    simpl. rewrite H0, H1. reflexivity.
  - (* E6 tgt *)
    apply wf_dim_sound in H0. apply wf_dim_sound in H1.
    simpl. rewrite H0, H1. reflexivity.
  - (* E7 comp *)
    apply wf_dim_sound in H1. apply wf_dim_sound in H2.
    rewrite H1, H2. reflexivity.
  - (* E8 id *)
    simpl. rewrite IHeq_cat. reflexivity.
  - (* IC1 : src(src x) == src(tgt x) *)
    apply wf_dim_sound in H. simpl. rewrite H.
    destruct n as [|[|n']]; try lia. reflexivity.
  - (* IC2 *)
    apply wf_dim_sound in H. simpl. rewrite H.
    destruct n as [|[|n']]; try lia. reflexivity.
  - (* IC3 : src(id x) == x *)
    apply wf_dim_sound in H. simpl. rewrite H. reflexivity.
  - (* IC4 : tgt(id x) == x *)
    apply wf_dim_sound in H. simpl. rewrite H. reflexivity.
  - (* IC5 : src(comp n y x) == src x *)
    apply wf_comp_inv in H. destruct H as (Hy & Hx & Hk & Hb).
    apply wf_dim_sound in Hx. apply wf_dim_sound in Hy.
    simpl. rewrite Hx, Hy.
    rewrite Nat.eqb_refl. simpl.
    assert (Hlt : n <? S n = true) by (apply Nat.ltb_lt; lia).
    rewrite Hlt. reflexivity.
  - (* IC6 : tgt(comp n y x) == tgt y *)
    apply wf_comp_inv in H. destruct H as (Hy & Hx & Hk & Hb).
    apply wf_dim_sound in Hx. apply wf_dim_sound in Hy.
    simpl. rewrite Hx, Hy.
    rewrite Nat.eqb_refl. simpl.
    assert (Hlt : n <? S n = true) by (apply Nat.ltb_lt; lia).
    rewrite Hlt. reflexivity.
  - (* IC7 : src(comp n y x) == comp n (src y) (src x) *)
    apply wf_comp_inv in H. destruct H as (Hy & Hx & Hk & Hb).
    apply wf_dim_sound in Hx. apply wf_dim_sound in Hy.
    simpl. rewrite Hx, Hy. rewrite Nat.eqb_refl. simpl.
    assert (Hlt : n <? d = true) by (apply Nat.ltb_lt; lia).
    rewrite Hlt.
    destruct d as [|d']; [lia|]. simpl.
    rewrite Nat.eqb_refl. simpl.
    assert (Hlt2 : n <? d' = true) by (apply Nat.ltb_lt; lia).
    rewrite Hlt2. reflexivity.
  - (* IC8 : tgt(comp n y x) == comp n (tgt y) (tgt x) *)
    apply wf_comp_inv in H. destruct H as (Hy & Hx & Hk & Hb).
    apply wf_dim_sound in Hx. apply wf_dim_sound in Hy.
    simpl. rewrite Hx, Hy. rewrite Nat.eqb_refl. simpl.
    assert (Hlt : n <? d = true) by (apply Nat.ltb_lt; lia).
    rewrite Hlt.
    destruct d as [|d']; [lia|]. simpl.
    rewrite Nat.eqb_refl. simpl.
    assert (Hlt2 : n <? d' = true) by (apply Nat.ltb_lt; lia).
    rewrite Hlt2. reflexivity.
  - (* IC9 assoc *)
    apply wf_dim_sound in H. apply wf_dim_sound in H0.
    rewrite H, H0. reflexivity.
  - (* IC10 exchange *)
    apply wf_dim_sound in H. apply wf_dim_sound in H0.
    rewrite H, H0. reflexivity.
  - (* IC11 left unit : comp n x (idext) == x *)
    apply wf_dim_sound in H1. apply wf_dim_sound in H.
    rewrite H1, H. reflexivity.
  - (* IC12 right unit *)
    apply wf_dim_sound in H1. apply wf_dim_sound in H.
    rewrite H1, H. reflexivity.
  - (* IC13 : id(comp n y x) == comp n (id y) (id x) *)
    apply wf_comp_inv in H. destruct H as (Hy & Hx & Hk & Hb).
    apply wf_dim_sound in Hx. apply wf_dim_sound in Hy.
    simpl. rewrite Hx, Hy. rewrite Nat.eqb_refl. simpl.
    assert (Hlt : n <? d = true) by (apply Nat.ltb_lt; lia).
    rewrite Hlt. rewrite Nat.eqb_refl. simpl.
    assert (Hlt2 : n <? S d = true) by (apply Nat.ltb_lt; lia).
    rewrite Hlt2. reflexivity.
Qed.

(** ** The dimension-agreement bridge used by [FreeModel.v]. *)
Lemma eq_cat_dim_agree : forall t1 t2 d1 d2,
  t1 == t2 -> wf t1 d1 -> wf t2 d2 -> d1 = d2.
Proof.
  intros t1 t2 d1 d2 Heq H1 H2.
  apply wf_dim_sound in H1. apply wf_dim_sound in H2.
  apply eq_cat_dim in Heq.
  rewrite H1 in Heq. rewrite H2 in Heq.
  injection Heq; auto.
Qed.
