(** * EckmannHilton.v
    The Eckmann–Hilton argument in dimension 2, derived in EqCat∞.

    Setting: a 0-cell [x] and 2-cells [p], [q] whose source and target are
    all [id x]. Then

      p ∘₁ q == p ∘₀ q == q ∘₁ p == q ∘₀ p.

    The argument has three steps: pad with the unit [u = id² x], apply
    exchange (IC10) once, remove the units. Everything else in this file is
    the bookkeeping those three steps rest on: each composite that is
    written down needs a [wf] derivation, and each [wf] of a composite
    needs a boundary equation. The lemmas are grouped so that the split is
    visible:

      §1  boundaries of the cells            (10 equations)
      §2  well-formedness of composites      (19 [wf] derivations,
                                              4 boundary equations)
      §3  unit laws in the form used         (4 equations)
      §4  the argument                       (2 theorems, 3 steps each)

    Part 1 proves the statement for arbitrary terms [x], [p], [q] with the
    boundary equations as hypotheses. It uses only constructors that
    [Presented.eq_cat] shares with [Axioms.eq_cat] (E1–E8, IC3–IC12): the
    same script compiles with [Include AxiomsF G] in place of
    [Include PresentedF G B]. Part 2 instantiates it on a concrete
    signature with generators α, β : id x ⇒ id x. *)

Require Import Arith Lia.
Require Import Syntax Presented.

Module EckmannHiltonF (G : GEN) (B : BDY G).
Include PresentedF G B.

Section EH.

Variable x : Term.
Hypothesis Hx : wf x 0.

Local Notation u := (id (id x)).

(** A 2-cell from [id x] to [id x]. *)
Definition loop2 (p : Term) : Prop :=
  wf p 2 /\ src p == id x /\ tgt p == id x.

(** ** §1 Boundaries. *)

Lemma wf_idx : wf (id x) 1.
Proof. wfs. Qed.

Lemma wf_u : wf u 2.
Proof. wfs. Qed.

Lemma s_u : src u == id x.
Proof. apply (IC3 (id x) 1 wf_idx). Qed.

Lemma t_u : tgt u == id x.
Proof. apply (IC4 (id x) 1 wf_idx). Qed.

Lemma ss_u : src (src u) == x.
Proof. apply (ss_id x 0 Hx). Qed.

Lemma tt_u : tgt (tgt u) == x.
Proof. apply (tt_id x 0 Hx). Qed.

Lemma ts_u : tgt (src u) == x.
Proof. apply (ts_id x 0 Hx). Qed.

Lemma st_u : src (tgt u) == x.
Proof. apply (st_id x 0 Hx). Qed.

Lemma ss_p : forall p, loop2 p -> src (src p) == x.
Proof.
  intros p (Hp & Hs & Ht). tr (src (id x)).
  - apply (E5_src _ _ 0 Hs); wfs.
  - apply (IC3 x 0 Hx).
Qed.

Lemma ts_p : forall p, loop2 p -> tgt (src p) == x.
Proof.
  intros p (Hp & Hs & Ht). tr (tgt (id x)).
  - apply (E6_tgt _ _ 0 Hs); wfs.
  - apply (IC4 x 0 Hx).
Qed.

Lemma st_p : forall p, loop2 p -> src (tgt p) == x.
Proof.
  intros p (Hp & Hs & Ht). tr (src (id x)).
  - apply (E5_src _ _ 0 Ht); wfs.
  - apply (IC3 x 0 Hx).
Qed.

Lemma tt_p : forall p, loop2 p -> tgt (tgt p) == x.
Proof.
  intros p (Hp & Hs & Ht). tr (tgt (id x)).
  - apply (E6_tgt _ _ 0 Ht); wfs.
  - apply (IC4 x 0 Hx).
Qed.

(** ** §2 Well-formedness of every composite the argument writes down. *)

(** [id x ∘₀ id x], the common boundary of the padded cells. *)
Lemma W_xx : wf (comp 0 (id x) (id x)) 1.
Proof.
  apply wf_comp; [wfs | wfs | lia |].
  change (src (id x) == tgt (id x)). tr x.
  - apply (IC3 x 0 Hx).
  - sy. apply (IC4 x 0 Hx).
Qed.

(** The two composites of the statement. *)
Lemma W1_pq : forall p q, loop2 p -> loop2 q -> wf (comp 1 p q) 2.
Proof.
  intros p q (Hp & Hsp & Htp) (Hq & Hsq & Htq).
  apply wf_comp; [exact Hp | exact Hq | lia |].
  change (src p == tgt q). tr (id x); [exact Hsp | sy; exact Htq].
Qed.

Lemma W0_pq : forall p q, loop2 p -> loop2 q -> wf (comp 0 p q) 2.
Proof.
  intros p q Lp Lq. pose proof Lp as (Hp & _). pose proof Lq as (Hq & _).
  apply wf_comp; [exact Hp | exact Hq | lia |].
  change (src (src p) == tgt (tgt q)). tr x; [apply ss_p, Lp | sy; apply tt_p, Lq].
Qed.

(** Horizontal padding: [p ∘₀ u] and [u ∘₀ p]. *)
Lemma W0_pu : forall p, loop2 p -> wf (comp 0 p u) 2.
Proof.
  intros p Lp. pose proof Lp as (Hp & _).
  apply wf_comp; [exact Hp | exact wf_u | lia |].
  change (src (src p) == tgt (tgt u)). tr x; [apply ss_p, Lp | sy; exact tt_u].
Qed.

Lemma W0_up : forall p, loop2 p -> wf (comp 0 u p) 2.
Proof.
  intros p Lp. pose proof Lp as (Hp & _).
  apply wf_comp; [exact wf_u | exact Hp | lia |].
  change (src (src u) == tgt (tgt p)). tr x; [exact ss_u | sy; apply tt_p, Lp].
Qed.

(** Vertical padding: [p ∘₁ u] and [u ∘₁ p]. *)
Lemma W1_pu : forall p, loop2 p -> wf (comp 1 p u) 2.
Proof.
  intros p (Hp & Hs & Ht).
  apply wf_comp; [exact Hp | exact wf_u | lia |].
  change (src p == tgt u). tr (id x); [exact Hs | sy; exact t_u].
Qed.

Lemma W1_up : forall p, loop2 p -> wf (comp 1 u p) 2.
Proof.
  intros p (Hp & Hs & Ht).
  apply wf_comp; [exact wf_u | exact Hp | lia |].
  change (src u == tgt p). tr (id x); [exact s_u | sy; exact Ht].
Qed.

(** The 1-dimensional composites that IC7/IC8 produce when the source or
    target of a horizontally padded cell is taken. *)
Lemma W_sp_su : forall p, loop2 p -> wf (comp 0 (src p) (src u)) 1.
Proof.
  intros p Lp. pose proof Lp as (Hp & _).
  apply wf_comp; [wfs | wfs | lia |].
  change (src (src p) == tgt (src u)). tr x; [apply ss_p, Lp | sy; exact ts_u].
Qed.

Lemma W_su_sp : forall p, loop2 p -> wf (comp 0 (src u) (src p)) 1.
Proof.
  intros p Lp. pose proof Lp as (Hp & _).
  apply wf_comp; [wfs | wfs | lia |].
  change (src (src u) == tgt (src p)). tr x; [exact ss_u | sy; apply ts_p, Lp].
Qed.

Lemma W_tp_tu : forall p, loop2 p -> wf (comp 0 (tgt p) (tgt u)) 1.
Proof.
  intros p Lp. pose proof Lp as (Hp & _).
  apply wf_comp; [wfs | wfs | lia |].
  change (src (tgt p) == tgt (tgt u)). tr x; [apply st_p, Lp | sy; exact tt_u].
Qed.

Lemma W_tu_tp : forall p, loop2 p -> wf (comp 0 (tgt u) (tgt p)) 1.
Proof.
  intros p Lp. pose proof Lp as (Hp & _).
  apply wf_comp; [wfs | wfs | lia |].
  change (src (tgt u) == tgt (tgt p)). tr x; [exact st_u | sy; apply tt_p, Lp].
Qed.

(** Source and target of the horizontally padded cells: all four are
    [id x ∘₀ id x] (IC7/IC8, then congruence). *)
Lemma S_pu : forall p, loop2 p -> src (comp 0 p u) == comp 0 (id x) (id x).
Proof.
  intros p Lp. pose proof Lp as (Hp & Hs & Ht).
  tr (comp 0 (src p) (src u)).
  - apply (IC7 u p 0 2 (W0_pu p Lp)). lia.
  - apply (E7_comp _ _ _ _ 0 1 Hs s_u (W_sp_su p Lp) W_xx).
Qed.

Lemma S_up : forall p, loop2 p -> src (comp 0 u p) == comp 0 (id x) (id x).
Proof.
  intros p Lp. pose proof Lp as (Hp & Hs & Ht).
  tr (comp 0 (src u) (src p)).
  - apply (IC7 p u 0 2 (W0_up p Lp)). lia.
  - apply (E7_comp _ _ _ _ 0 1 s_u Hs (W_su_sp p Lp) W_xx).
Qed.

Lemma T_pu : forall p, loop2 p -> tgt (comp 0 p u) == comp 0 (id x) (id x).
Proof.
  intros p Lp. pose proof Lp as (Hp & Hs & Ht).
  tr (comp 0 (tgt p) (tgt u)).
  - apply (IC8 u p 0 2 (W0_pu p Lp)). lia.
  - apply (E7_comp _ _ _ _ 0 1 Ht t_u (W_tp_tu p Lp) W_xx).
Qed.

Lemma T_up : forall p, loop2 p -> tgt (comp 0 u p) == comp 0 (id x) (id x).
Proof.
  intros p Lp. pose proof Lp as (Hp & Hs & Ht).
  tr (comp 0 (tgt u) (tgt p)).
  - apply (IC8 p u 0 2 (W0_up p Lp)). lia.
  - apply (E7_comp _ _ _ _ 0 1 t_u Ht (W_tu_tp p Lp) W_xx).
Qed.

(** The two sides of the exchange instance [(p ∘₀ u) ∘₁ (u ∘₀ q) == (p ∘₁ u) ∘₀ (u ∘₁ q)]. *)
Lemma W_exL : forall p q, loop2 p -> loop2 q ->
  wf (comp 1 (comp 0 p u) (comp 0 u q)) 2.
Proof.
  intros p q Lp Lq.
  apply wf_comp; [apply W0_pu, Lp | apply W0_up, Lq | lia |].
  change (src (comp 0 p u) == tgt (comp 0 u q)).
  tr (comp 0 (id x) (id x)); [apply S_pu, Lp | sy; apply T_up, Lq].
Qed.

Lemma W_exR : forall p q, loop2 p -> loop2 q ->
  wf (comp 0 (comp 1 p u) (comp 1 u q)) 2.
Proof.
  intros p q Lp Lq.
  apply wf_comp; [apply W1_pu, Lp | apply W1_up, Lq | lia |].
  change (src (src (comp 1 p u)) == tgt (tgt (comp 1 u q))). tr x.
  - tr (src (src u)); [| exact ss_u].
    apply (E5_src _ _ 0 (IC5 u p 1 (W1_pu p Lp))); [| wfs].
    apply wf_src, W1_pu, Lp.
  - sy. tr (tgt (tgt u)); [| exact tt_u].
    apply (E6_tgt _ _ 0 (IC6 q u 1 (W1_up q Lq))); [| wfs].
    apply wf_tgt, W1_up, Lq.
Qed.

(** The two sides of the mirrored instance [(u ∘₀ p) ∘₁ (q ∘₀ u) == (u ∘₁ q) ∘₀ (p ∘₁ u)]. *)
Lemma W_exL' : forall p q, loop2 p -> loop2 q ->
  wf (comp 1 (comp 0 u p) (comp 0 q u)) 2.
Proof.
  intros p q Lp Lq.
  apply wf_comp; [apply W0_up, Lp | apply W0_pu, Lq | lia |].
  change (src (comp 0 u p) == tgt (comp 0 q u)).
  tr (comp 0 (id x) (id x)); [apply S_up, Lp | sy; apply T_pu, Lq].
Qed.

Lemma W_exR' : forall p q, loop2 p -> loop2 q ->
  wf (comp 0 (comp 1 u q) (comp 1 p u)) 2.
Proof.
  intros p q Lp Lq. pose proof Lp as (Hp & _). pose proof Lq as (Hq & _).
  apply wf_comp; [apply W1_up, Lq | apply W1_pu, Lp | lia |].
  change (src (src (comp 1 u q)) == tgt (tgt (comp 1 p u))). tr x.
  - tr (src (src q)); [| apply ss_p, Lq].
    apply (E5_src _ _ 0 (IC5 q u 1 (W1_up q Lq))); [| wfs].
    apply wf_src, W1_up, Lq.
  - sy. tr (tgt (tgt p)); [| apply tt_p, Lp].
    apply (E6_tgt _ _ 0 (IC6 u p 1 (W1_pu p Lp))); [| wfs].
    apply wf_tgt, W1_pu, Lp.
Qed.

(** The unit composites in the literal shape of IC11/IC12. *)
Lemma W_unitR0 : forall p, loop2 p -> wf (comp 0 p (id (id (src (src p))))) 2.
Proof.
  intros p (Hp & _). apply wf_comp; [exact Hp | wfs | lia |].
  change (src (src p) == tgt (tgt (id (id (src (src p)))))).
  sy. apply (tt_id _ 0). wfs.
Qed.

Lemma W_unitL0 : forall p, loop2 p -> wf (comp 0 (id (id (tgt (tgt p)))) p) 2.
Proof.
  intros p (Hp & _). apply wf_comp; [wfs | exact Hp | lia |].
  change (src (src (id (id (tgt (tgt p))))) == tgt (tgt p)).
  apply (ss_id _ 0). wfs.
Qed.

Lemma W_unitR1 : forall p, loop2 p -> wf (comp 1 p (id (src p))) 2.
Proof.
  intros p (Hp & _). apply wf_comp; [exact Hp | wfs | lia |].
  change (src p == tgt (id (src p))). sy. apply (IC4 _ 1). wfs.
Qed.

Lemma W_unitL1 : forall p, loop2 p -> wf (comp 1 (id (tgt p)) p) 2.
Proof.
  intros p (Hp & _). apply wf_comp; [wfs | exact Hp | lia |].
  change (src (id (tgt p)) == tgt p). apply (IC3 _ 1). wfs.
Qed.

(** ** §3 Unit laws with the unit written as [u]. *)

Lemma UR0 : forall p, loop2 p -> comp 0 p u == p.
Proof.
  intros p Lp. pose proof Lp as (Hp & _).
  tr (comp 0 p (id (id (src (src p))))).
  - apply (E7_comp _ _ _ _ 0 2 (E1_refl p)); [| apply W0_pu, Lp | apply W_unitR0, Lp].
    apply E8_id, E8_id. sy. apply ss_p, Lp.
  - exact (IC11 p 0 2 Hp ltac:(lia) (W_unitR0 p Lp)).
Qed.

Lemma UL0 : forall p, loop2 p -> comp 0 u p == p.
Proof.
  intros p Lp. pose proof Lp as (Hp & _).
  tr (comp 0 (id (id (tgt (tgt p)))) p).
  - apply (E7_comp _ _ _ _ 0 2); [| apply E1_refl | apply W0_up, Lp | apply W_unitL0, Lp].
    apply E8_id, E8_id. sy. apply tt_p, Lp.
  - exact (IC12 p 0 2 Hp ltac:(lia) (W_unitL0 p Lp)).
Qed.

Lemma UR1 : forall p, loop2 p -> comp 1 p u == p.
Proof.
  intros p Lp. pose proof Lp as (Hp & Hs & _).
  tr (comp 1 p (id (src p))).
  - apply (E7_comp _ _ _ _ 1 2 (E1_refl p)); [| apply W1_pu, Lp | apply W_unitR1, Lp].
    apply E8_id. sy. exact Hs.
  - exact (IC11 p 1 2 Hp ltac:(lia) (W_unitR1 p Lp)).
Qed.

Lemma UL1 : forall p, loop2 p -> comp 1 u p == p.
Proof.
  intros p Lp. pose proof Lp as (Hp & _ & Ht).
  tr (comp 1 (id (tgt p)) p).
  - apply (E7_comp _ _ _ _ 1 2); [| apply E1_refl | apply W1_up, Lp | apply W_unitL1, Lp].
    apply E8_id. sy. exact Ht.
  - exact (IC12 p 1 2 Hp ltac:(lia) (W_unitL1 p Lp)).
Qed.

(** ** §4 The argument. *)

(** Vertical and horizontal composition agree. *)
Theorem EH_main : forall p q, loop2 p -> loop2 q -> comp 1 p q == comp 0 p q.
Proof.
  intros p q Lp Lq.
  (* pad with units *)
  tr (comp 1 (comp 0 p u) (comp 0 u q)).
  { apply (E7_comp _ _ _ _ 1 2); [sy; apply UR0, Lp | sy; apply UL0, Lq | |].
    - apply W1_pq; assumption.
    - apply W_exL; assumption. }
  (* exchange *)
  tr (comp 0 (comp 1 p u) (comp 1 u q)).
  { apply (IC10 p u u q 1 0 2); [apply W_exL | apply W_exR]; assumption. }
  (* remove units *)
  apply (E7_comp _ _ _ _ 0 2); [apply UR1, Lp | apply UL1, Lq | |].
  - apply W_exR; assumption.
  - apply W0_pq; assumption.
Qed.

(** The same argument with the units on the other sides swaps the operands. *)
Theorem EH_mirror : forall p q, loop2 p -> loop2 q -> comp 1 p q == comp 0 q p.
Proof.
  intros p q Lp Lq.
  tr (comp 1 (comp 0 u p) (comp 0 q u)).
  { apply (E7_comp _ _ _ _ 1 2); [sy; apply UL0, Lp | sy; apply UR0, Lq | |].
    - apply W1_pq; assumption.
    - apply W_exL'; assumption. }
  tr (comp 0 (comp 1 u q) (comp 1 p u)).
  { apply (IC10 u p q u 1 0 2); [apply W_exL' | apply W_exR']; assumption. }
  apply (E7_comp _ _ _ _ 0 2); [apply UL1, Lq | apply UR1, Lp | |].
  - apply W_exR'; assumption.
  - apply W0_pq; assumption.
Qed.

(** Both compositions are commutative. *)
Corollary EH_comm1 : forall p q, loop2 p -> loop2 q -> comp 1 p q == comp 1 q p.
Proof.
  intros p q Lp Lq. tr (comp 0 p q).
  - apply EH_main; assumption.
  - sy. apply EH_mirror; assumption.
Qed.

Corollary EH_comm0 : forall p q, loop2 p -> loop2 q -> comp 0 p q == comp 0 q p.
Proof.
  intros p q Lp Lq. tr (comp 1 p q).
  - sy. apply EH_main; assumption.
  - apply EH_mirror; assumption.
Qed.

End EH.

End EckmannHiltonF.

(** ** Part 2. A concrete signature: one 0-cell and two 2-cells on its identity. *)

Module EHGen <: GEN.
  Inductive G := x | alpha | beta.
  Definition Generator := G.
  Definition gen_dim (g : G) : nat :=
    match g with x => 0 | alpha => 2 | beta => 2 end.
  Definition Generator_eq_dec : forall g1 g2 : Generator, {g1 = g2} + {g1 <> g2}.
  Proof. decide equality. Defined.
End EHGen.

Module EHBdy <: BDY EHGen.
  Module Syn := SyntaxF EHGen.
  (** α, β : id x ⇒ id x. *)
  Definition gen_bd (g : EHGen.Generator) : option (Syn.Term * Syn.Term) :=
    match g with
    | EHGen.x => None
    | _ => Some (Syn.id (Syn.gen EHGen.x), Syn.id (Syn.gen EHGen.x))
    end.
End EHBdy.

Module EH := EckmannHiltonF EHGen EHBdy.
Import EH.

Notation x     := (gen EHGen.x).
Notation alpha := (gen EHGen.alpha).
Notation beta  := (gen EHGen.beta).

Lemma wf_x : wf x 0.
Proof. exact (wf_gen0 EHGen.x eq_refl). Qed.

Lemma wf_alpha : wf alpha 2.
Proof. apply (wf_genB EHGen.alpha (id x) (id x) 1); try reflexivity; wfs; exact wf_x. Qed.

Lemma wf_beta : wf beta 2.
Proof. apply (wf_genB EHGen.beta (id x) (id x) 1); try reflexivity; wfs; exact wf_x. Qed.

Lemma loop2_alpha : loop2 x alpha.
Proof.
  repeat split; [exact wf_alpha | |].
  - apply (B_src EHGen.alpha (id x) (id x) 1 eq_refl wf_alpha).
  - apply (B_tgt EHGen.alpha (id x) (id x) 1 eq_refl wf_alpha).
Qed.

Lemma loop2_beta : loop2 x beta.
Proof.
  repeat split; [exact wf_beta | |].
  - apply (B_src EHGen.beta (id x) (id x) 1 eq_refl wf_beta).
  - apply (B_tgt EHGen.beta (id x) (id x) 1 eq_refl wf_beta).
Qed.

Theorem eckmann_hilton_vertical_is_horizontal : comp 1 alpha beta == comp 0 alpha beta.
Proof. exact (EH_main x wf_x alpha beta loop2_alpha loop2_beta). Qed.

Theorem eckmann_hilton_vertical_commutes : comp 1 alpha beta == comp 1 beta alpha.
Proof. exact (EH_comm1 x wf_x alpha beta loop2_alpha loop2_beta). Qed.

Theorem eckmann_hilton_horizontal_commutes : comp 0 alpha beta == comp 0 beta alpha.
Proof. exact (EH_comm0 x wf_x alpha beta loop2_alpha loop2_beta). Qed.

Print Assumptions eckmann_hilton_vertical_is_horizontal.
Print Assumptions eckmann_hilton_vertical_commutes.
Print Assumptions eckmann_hilton_horizontal_commutes.
