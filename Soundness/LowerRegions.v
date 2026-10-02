(** Finite lower-certificate representation. The m-by-m block uses the
    shared nat-indexed folds; inactive rows and columns are padded with zero.
    This file proves one-step bounds, not matrix decay or while soundness. *)
From Stdlib Require Import Reals Lra Lia.
From mathcomp Require Import kernel.
Require Import CPHL Soundness.FiniteExpectationBounds Soundness.RegionMeasureFacts.
Import ValuationSpace CommandSemantics.
Open Scope R_scope.

Definition region_active (m : nat) (regions : nat -> CFormula) (i : nat) : Prop :=
  (i < m)%nat /\ exists v : Valuation, satisfies v (regions i).
(** Inhabitation quantifies over all valuations; a pointwise formula
    evaluator is insufficient. Use MathComp's existing classical decision. *)
Definition region_active_dec m regions i := boolp.pselect (region_active m regions i).
Definition lower_positive (r : R) : R := Rmax 0 r.
Definition lower_transition m regions (transitions : nat -> nat -> R) i j : R :=
  if region_active_dec m regions i then
    if region_active_dec m regions j then lower_positive (transitions i j) else 0
  else 0.
Definition lower_exit m regions (exits : nat -> R) i : R :=
  if region_active_dec m regions i then lower_positive (exits i) else 0.
Definition lower_value m regions (solution : nat -> R) i : R :=
  if region_active_dec m regions i then solution i else 0.

Lemma lower_positive_nonnegative r : 0 <= lower_positive r.
Proof. unfold lower_positive, Rmax; destruct (Rle_dec 0 r); lra. Qed.
Lemma lower_positive_ge r : r <= lower_positive r.
Proof. unfold lower_positive, Rmax; destruct (Rle_dec 0 r); lra. Qed.
Lemma lower_positive_le r b : 0 <= b -> r <= b -> lower_positive r <= b.
Proof. unfold lower_positive, Rmax; destruct (Rle_dec 0 r); lra. Qed.
Lemma lower_positive_positive r : 0 < r -> 0 < lower_positive r.
Proof. pose proof (lower_positive_ge r); lra. Qed.

Lemma lower_transition_active m regions transitions i j :
  region_active m regions i -> region_active m regions j ->
  lower_transition m regions transitions i j = lower_positive (transitions i j).
Proof. unfold lower_transition; destruct (region_active_dec m regions i); destruct (region_active_dec m regions j); tauto. Qed.
Lemma lower_transition_inactive_source m regions transitions i :
  ~ region_active m regions i -> forall j, lower_transition m regions transitions i j = 0.
Proof. unfold lower_transition; destruct (region_active_dec m regions i); tauto. Qed.
Lemma lower_transition_inactive_target m regions transitions i j :
  ~ region_active m regions j -> lower_transition m regions transitions i j = 0.
Proof. unfold lower_transition; destruct (region_active_dec m regions i); destruct (region_active_dec m regions j); tauto. Qed.
Lemma lower_exit_active m regions exits i : region_active m regions i ->
  lower_exit m regions exits i = lower_positive (exits i).
Proof. unfold lower_exit; destruct (region_active_dec m regions i); tauto. Qed.
Lemma lower_exit_inactive m regions exits i : ~ region_active m regions i ->
  lower_exit m regions exits i = 0.
Proof. unfold lower_exit; destruct (region_active_dec m regions i); tauto. Qed.
Lemma lower_value_active m regions solution i : region_active m regions i ->
  lower_value m regions solution i = solution i.
Proof. unfold lower_value; destruct (region_active_dec m regions i); tauto. Qed.
Lemma lower_value_inactive m regions solution i : ~ region_active m regions i ->
  lower_value m regions solution i = 0.
Proof. unfold lower_value; destruct (region_active_dec m regions i); tauto. Qed.
Lemma lower_transition_nonnegative m regions transitions i j :
  0 <= lower_transition m regions transitions i j.
Proof.
  unfold lower_transition; destruct (region_active_dec m regions i); try lra.
  destruct (region_active_dec m regions j); [apply lower_positive_nonnegative|lra].
Qed.
Lemma lower_exit_nonnegative m regions exits i : 0 <= lower_exit m regions exits i.
Proof. unfold lower_exit; destruct (region_active_dec m regions i); [apply lower_positive_nonnegative|lra]. Qed.

Section Certificate.
Context (m : nat) (g : CFormula) (body : Cmd) (q : PConstruct)
  (regions : nat -> CFormula) (transitions : nat -> nat -> R) (exits : nat -> R).
Hypothesis body_valid : forall i, (i < m)%nat -> hoare_valid
  (p_concentrated_mass (regions i) (PConst 1)) body
  (while_body_post_lower m regions (transitions i) g q (exits i)).

(** Negative raw lower bounds convey no information beyond nonnegativity.
    Replacing them by zero is justified separately for each kernel output. *)
Lemma lower_point_bounds i (v : Valuation) : (i < m)%nat -> satisfies v (regions i) ->
  (forall j, (j < m)%nat -> lower_transition m regions transitions i j <=
    expectation (denote body v) (q_eval (QIndicator (regions j)))) /\
  lower_exit m regions exits i <=
    expectation (denote body v) (q_eval (condition_pconstruct q (c_not g))).
Proof.
  intros hi hv.
  pose proof (while_lower_body_point m g body q regions transitions exits body_valid i v hi hv) as [ht hx].
  assert (ha : region_active m regions i) by (split; [exact hi|exists v; exact hv]).
  split.
  - intros j hj; destruct (region_active_dec m regions j) as [hjactive|hjempty].
    + rewrite lower_transition_active by assumption; apply lower_positive_le.
      * exact (proj1 (kernel_reward_bounds (denote body) (QIndicator (regions j)) v)).
      * apply ht; exact hj.
    + rewrite lower_transition_inactive_target by assumption.
      exact (proj1 (kernel_reward_bounds (denote body) (QIndicator (regions j)) v)).
  - rewrite lower_exit_active by assumption; apply lower_positive_le.
    + exact (proj1 (kernel_reward_bounds (denote body) (condition_pconstruct q (c_not g)) v)).
    + exact hx.
Qed.

(** Empty target events have mass zero. An active source therefore cannot
    have a strictly positive raw lower coefficient into such a target. *)
Lemma lower_empty_target_coefficient i j : region_active m regions i -> (j < m)%nat ->
  ~ region_active m regions j -> transitions i j <= 0.
Proof.
  intros [hi [v hv] ] hj he.
  pose proof (while_lower_body_point m g body q regions transitions exits body_valid i v hi hv) as [ht hx].
  specialize (ht j hj).
  assert (hempty : forall w, ~ satisfies w (regions j)).
  { intros w hw; apply he; split; [exact hj|exists w; exact hw]. }
  rewrite (empty_region_expectation _ _ hempty) in ht; exact ht.
Qed.

Lemma lower_positive_transition_active i j : region_active m regions i ->
  (j < m)%nat -> 0 < transitions i j -> region_active m regions j.
Proof.
  intros hi hj hp; destruct (region_active_dec m regions j) as [ha|he]; first exact ha.
  pose proof (lower_empty_target_coefficient i j hi hj he); lra.
Qed.

(** Derive the row budget only from an inhabited source. Disjointness and
    guard containment bound the actual outputs; coverage is unnecessary. *)
Theorem lower_matrix_reward_budget : while_regions_disjoint m regions ->
  while_regions_in_guard m g regions -> forall i,
  finite_r_sum m (lower_transition m regions transitions i) + lower_exit m regions exits i <= 1.
Proof.
  intros hd hg i; destruct (region_active_dec m regions i) as [ [hi [v hv] ]|he].
  - pose proof (lower_point_bounds i v hi hv) as [ht hx].
    pose proof (finite_r_sum_le m _ _ ht) as hs.
    pose proof (kernel_region_reward_budget m g regions q (denote body) v hd hg) as hb.
    lra.
  - rewrite lower_exit_inactive by assumption.
    rewrite (finite_r_sum_zero m _ (fun j _ => lower_transition_inactive_source m regions transitions i he j)); lra.
Qed.

Corollary lower_matrix_substochastic : while_regions_disjoint m regions ->
  while_regions_in_guard m g regions -> forall i,
  0 <= finite_r_sum m (lower_transition m regions transitions i) <= 1.
Proof.
  intros hd hg i; split.
  - apply finite_r_sum_nonnegative; intros; apply lower_transition_nonnegative.
  - pose proof (lower_matrix_reward_budget hd hg i).
    pose proof (lower_exit_nonnegative m regions exits i); lra.
Qed.

(** All masses, including zero, are treated by integration of pointwise
    bounds. This avoids a normalization precondition and preserves correlation. *)
Theorem lower_concentrated_body i ps : (i < m)%nat -> pstate_admissible ps ->
  psatisfies ps (p_almost_sure (regions i)) ->
  (forall j, (j < m)%nat ->
    lower_transition m regions transitions i j * measure_of (pstate_measure ps) (fun _ => True) <=
    expectation (pstate_measure (run body ps)) (q_eval (QIndicator (regions j)))) /\
  lower_exit m regions exits i * measure_of (pstate_measure ps) (fun _ => True) <=
    expectation (pstate_measure (run body ps)) (q_eval (condition_pconstruct q (c_not g))).
Proof.
  intros hi hp hreg; split.
  - intros j hj; apply (concentrated_kernel_reward_lower (denote body) (regions i) (QIndicator (regions j))).
    + exact hp.
    + exact hreg.
    + apply lower_transition_nonnegative.
    + intros v hv; exact (proj1 (lower_point_bounds i v hi hv) j hj).
  - apply (concentrated_kernel_reward_lower (denote body) (regions i) (condition_pconstruct q (c_not g))).
    + exact hp.
    + exact hreg.
    + apply lower_exit_nonnegative.
    + intros v hv; exact (proj2 (lower_point_bounds i v hi hv)).
Qed.

(** Mask the proposed solution as well. Dropping an empty target removes
    a nonpositive summand; replacing active coefficients by positive parts
    increases the right side because the original solution is nonnegative. *)
Theorem lower_masked_solution solution : while_lower_solution m solution transitions exits ->
  while_lower_solution m (lower_value m regions solution)
    (lower_transition m regions transitions) (lower_exit m regions exits).
Proof.
  intros hs i hi; destruct (region_active_dec m regions i) as [ha|he].
  - rewrite lower_value_active by assumption; destruct (hs i hi) as [hineq hbounds]; split; last exact hbounds.
    assert (hrows : finite_r_sum m (fun j => transitions i j * solution j) <=
      finite_r_sum m (fun j => lower_transition m regions transitions i j * lower_value m regions solution j)).
    { apply finite_r_sum_le; intros j hj.
      destruct (region_active_dec m regions j) as [hja|hje].
      - rewrite lower_transition_active, lower_value_active by assumption.
        apply Rmult_le_compat_r; [exact (proj1 (proj2 (hs j hj)))|apply lower_positive_ge].
      - rewrite lower_transition_inactive_target, lower_value_inactive by assumption.
        pose proof (lower_empty_target_coefficient i j ha hj hje).
        pose proof (proj1 (proj2 (hs j hj))); nra. }
    rewrite lower_exit_active by assumption; pose proof (lower_positive_ge (exits i)); lra.
  - rewrite lower_value_inactive, lower_exit_inactive by assumption.
    rewrite (finite_r_sum_zero m (fun j => lower_transition m regions transitions i j * lower_value m regions solution j)).
    + split; lra.
    + intros j hj; rewrite lower_transition_inactive_source by assumption; ring.
Qed.

(** Progress stays within active regions. These are one-step transfer
    lemmas only; the path, contraction, and residual limits belong to task 10. *)
Lemma lower_active_progress : while_progress m transitions exits ->
  forall i, region_active m regions i ->
  0 < lower_exit m regions exits i \/
  exists j, (j < i)%nat /\ region_active m regions j /\ 0 < lower_transition m regions transitions i j.
Proof.
  intros hp i ha; destruct (hp i (proj1 ha)) as [hx|[j [hj ht] ] ].
  - left; rewrite lower_exit_active by assumption; apply lower_positive_positive; exact hx.
  - right; assert (hja : region_active m regions j).
    { apply lower_positive_transition_active with (i:=i); try assumption; pose proof (proj1 ha); lia. }
    exists j; split; [exact hj|split; [exact hja|] ].
    rewrite lower_transition_active by assumption; apply lower_positive_positive; exact ht.
Qed.

(** Zero padding gives inactive rows unit deficit. The full finite block
    therefore has progress measured by its deficit, ready for matrix decay. *)
Theorem lower_deficit_progress : while_regions_disjoint m regions ->
  while_regions_in_guard m g regions -> while_progress m transitions exits ->
  forall i, (i < m)%nat ->
  0 < 1 - finite_r_sum m (lower_transition m regions transitions i) \/
  exists j, (j < i)%nat /\ 0 < lower_transition m regions transitions i j.
Proof.
  intros hd hg hp i hi; destruct (region_active_dec m regions i) as [ha|he].
  - destruct (lower_active_progress hp i ha) as [hx|[j [hj [hja ht] ] ] ].
    + left; pose proof (lower_matrix_reward_budget hd hg i); lra.
    + right; exists j; auto.
  - left; rewrite (finite_r_sum_zero m _ (fun j _ => lower_transition_inactive_source m regions transitions i he j)); lra.
Qed.
End Certificate.
