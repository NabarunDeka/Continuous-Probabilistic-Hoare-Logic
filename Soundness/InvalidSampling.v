(** Invalid sampling annihilates any input concentrated on invalid parameter
    states. Concentration is almost sure: valid states of zero mass are allowed. *)
From Stdlib Require Import Reals.
Require Import CPHL Soundness.AssertionLogic Soundness.AtomicCommandFacts
  Soundness.DistributionFacts Soundness.CommandFacts Soundness.Conditioning
  Soundness.ConditioningAssertions
  Soundness.InputDecomposition.
Import CommandSemantics.

(** The stronger expectation identity applies to every bounded construct,
    including nested integrals and distributions depending on the old x. *)
Lemma run_sample_invalid_expectation x d ps q :
  pstate_admissible ps ->
  psatisfies ps (p_almost_sure (c_not (distribution_valid_formula d))) ->
  expectation (pstate_measure (run (CRealSample x d) ps)) (q_eval q) = 0%R.
Proof.
  intros Hps Hinvalid.
  transitivity (expectation (pstate_measure ps) (q_eval (QIntegral x d q))).
  { apply transform_sample_q_eval; exact Hps. }
  pose proof (@almost_sure_restriction_equiv
    (c_not (distribution_valid_formula d)) ps Hps Hinvalid) as [Hmu Hrho].
  rewrite <- (@expectation_measure_equiv _ _
    (q_eval (QIntegral x d q)) Hmu).
  cbn [condition_state pstate_measure].
  rewrite <- condition_expectation_correct.
  transitivity (expectation (pstate_measure ps) (fun _ => 0%R)).
  - apply expectation_extensional; intro v.
    rewrite condition_pconstruct_correct.
    destruct (boolp.pselect (distribution_valid d v)) as [Hv | Hv].
    + rewrite (real_indicator_false
        (satisfies v (c_not (distribution_valid_formula d)))).
      * apply Rmult_0_l.
      * intro H; apply H; apply distribution_valid_formula_spec; exact Hv.
    + rewrite (@q_integral_invalid x d q v Hv); apply Rmult_0_r.
  - apply expectation_zero.
Qed.

Lemma hoare_valid_real_sample_invalid pre x d :
  pformula_valid
    (PFImpl pre (p_almost_sure (c_not (distribution_valid_formula d)))) ->
  hoare_valid pre (CRealSample x d)
    (p_eq (PExpect (QIndicator c_true)) (PConst 0%R)).
Proof.
  intros Hpre ps Hps Heta.
  apply (proj2 (psatisfies_eq _ _ _)); cbn [pterm_eval].
  apply run_sample_invalid_expectation; [exact Hps | exact (Hpre ps Hps Heta)].
Qed.
