(** Instantiate finite matrix decay for task 9's lower representation.
    This file makes no claim that matrix rewards already bound the loop's
    finite semantic rewards; that connection belongs to task 11. *)
From Stdlib Require Import Reals Lra Lia.
Require Import CPHL Soundness.LowerRegions Soundness.FiniteMatrix Soundness.MatrixDecay.
Open Scope R_scope.

Section LowerCertificate.
Context (m : nat) (g : CFormula) (body : Cmd) (q : PConstruct)
  (regions : nat -> CFormula) (transitions : nat -> nat -> R) (exits : nat -> R).
Hypothesis body_valid : forall i, (i < m)%nat -> hoare_valid
  (p_concentrated_mass (regions i) (PConst 1)) body
  (while_body_post_lower m regions (transitions i) g q (exits i)).
Hypothesis disjoint : while_regions_disjoint m regions.
Hypothesis guarded : while_regions_in_guard m g regions.
Hypothesis progress : while_progress m transitions exits.

Lemma lower_certificate_substochastic :
  matrix_substochastic m (lower_transition m regions transitions).
Proof.
  split.
  - intros i j hi hj; apply lower_transition_nonnegative.
  - intros i hi; exact (proj2 (lower_matrix_substochastic m g body q regions transitions exits
      body_valid disjoint guarded i)).
Qed.
Lemma lower_certificate_progress :
  matrix_deficit_progress m (lower_transition m regions transitions).
Proof.
  exact (lower_deficit_progress m g body q regions transitions exits body_valid disjoint guarded progress).
Qed.

Lemma lower_certificate_rewards_bounds n i : (i < m)%nat ->
  0 <= matrix_rewards m (lower_transition m regions transitions)
    (lower_exit m regions exits) n i <= 1.
Proof.
  apply matrix_rewards_bounds.
  - apply lower_certificate_substochastic.
  - intros; apply lower_exit_nonnegative.
  - intros j hj; pose proof (lower_matrix_reward_budget m g body q regions transitions exits
      body_valid disjoint guarded j); lra.
Qed.

(** The same contraction constant serves every index, including zero-padded
    empty rows. It depends on the finite certificate, not on an input measure. *)
Theorem lower_certificate_contraction :
  exists c, 0 <= c < 1 /\ forall i, (i < m)%nat ->
    matrix_survival m (lower_transition m regions transitions) m i <= c.
Proof. apply matrix_uniform_contraction; [apply lower_certificate_substochastic|apply lower_certificate_progress]. Qed.
Theorem lower_certificate_decay i : (i < m)%nat ->
  Un_cv (fun n => matrix_survival m (lower_transition m regions transitions) n i) 0.
Proof. apply matrix_survival_tends_zero; [apply lower_certificate_substochastic|apply lower_certificate_progress]. Qed.

Context (solution : nat -> R).
Hypothesis solution_valid : while_lower_solution m solution transitions exits.

Lemma lower_certificate_residual i : (i < m)%nat ->
  Un_cv (fun n => matrix_power_apply m (lower_transition m regions transitions) n
    (lower_value m regions solution) i) 0.
Proof.
  apply matrix_residual_tends_zero.
  - apply lower_certificate_substochastic.
  - apply lower_certificate_progress.
  - intros j hj; exact (proj2 (lower_masked_solution m g body q regions transitions exits
      body_valid solution solution_valid j hj)).
Qed.

Lemma lower_certificate_finite_bound n i : (i < m)%nat ->
  lower_value m regions solution i <=
    matrix_rewards m (lower_transition m regions transitions) (lower_exit m regions exits) n i +
    matrix_power_apply m (lower_transition m regions transitions) n (lower_value m regions solution) i.
Proof.
  apply matrix_subsolution_residual.
  - intros u v hu hv; apply lower_transition_nonnegative.
  - intros j hj; pose proof (proj1 (lower_masked_solution m g body q regions transitions exits
      body_valid solution solution_valid j hj)) as h.
    unfold matrix_apply; lra.
Qed.

(** Clipping and masking give a certified geometric error for the original
    proposed value on every inhabited source. No body-termination claim follows. *)
Theorem lower_certificate_geometric_bound :
  exists c, 0 <= c < 1 /\ forall n i, region_active m regions i ->
    solution i <= matrix_rewards m (lower_transition m regions transitions)
      (lower_exit m regions exits) n i + c ^ (n / m).
Proof.
  destruct lower_certificate_contraction as [c [hc hb] ]; exists c; split; first exact hc.
  intros n i ha; pose proof (lower_certificate_finite_bound n i (proj1 ha)) as h.
  rewrite lower_value_active in h by assumption.
  pose proof (matrix_power_le m (lower_transition m regions transitions) n
    (lower_value m regions solution) (fun _ => 1)
    (proj1 lower_certificate_substochastic)) as hpow.
  assert (hupper : forall j, (j < m)%nat -> lower_value m regions solution j <= 1).
  { intros j hj; exact (proj2 (proj2 (lower_masked_solution m g body q regions transitions exits
      body_valid solution solution_valid j hj))). }
  specialize (hpow hupper i (proj1 ha)).
  pose proof (matrix_survival_geometric m (lower_transition m regions transitions) c
    lower_certificate_substochastic (proj1 hc) hb n i (proj1 ha)) as hgeom.
  unfold matrix_survival in hgeom; lra.
Qed.

(** A later semantic proof need only dominate these finite matrix rewards
    at its selected point and supply convergence to the loop's reward. *)
Theorem lower_certificate_reward_limit i rewards limit :
  region_active m regions i ->
  (forall n, matrix_rewards m (lower_transition m regions transitions)
    (lower_exit m regions exits) n i <= rewards n) ->
  Un_cv rewards limit -> solution i <= limit.
Proof.
  intros ha hr hl; rewrite <- (lower_value_active m regions solution i ha).
  apply (matrix_subsolution_limit_at m (lower_transition m regions transitions)
    (lower_exit m regions exits) (lower_value m regions solution) i rewards limit).
  - apply lower_certificate_substochastic.
  - apply lower_certificate_progress.
  - intros j hj; exact (proj2 (lower_masked_solution m g body q regions transitions exits
      body_valid solution solution_valid j hj)).
  - intros j hj; pose proof (proj1 (lower_masked_solution m g body q regions transitions exits
      body_valid solution solution_valid j hj)) as h; unfold matrix_apply; lra.
  - exact (proj1 ha).
  - exact hr.
  - exact hl.
Qed.
End LowerCertificate.
