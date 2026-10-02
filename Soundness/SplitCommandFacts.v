(** The IF and SUM output decompositions follow from command kernels.
    The component commands may themselves contain loops or lose mass. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals topology ereal measure.
From mathcomp Require Import lebesgue_stieltjes_measure Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.CommandFacts Soundness.TransformerFacts
  Soundness.AssertionLogic Soundness.ConditioningAssertions Soundness.InputDecomposition.

Import numFieldTopology.Exports MeasurableR ValuationSpace CommandSemantics.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Negating the guard denotes the complement event. At the event interface,
    the restriction proofs do not affect the measure values. *)
Lemma run_if_measure_equiv guard c1 c2 ps :
  measure_equiv (pstate_measure (run (CIf guard c1 c2) ps))
    (ConcreteMeasure.add
      (pstate_measure (run c1 (condition_state guard ps)))
      (pstate_measure (run c2 (condition_state (c_not guard) ps)))).
Proof.
  move=> A mA.
  transitivity
    (pstate_measure (run c1 (condition_state guard ps)) A +
     pstate_measure (run c2 (condition_state (c_not guard) ps)) A).
  - exact: transform_branch.
  - symmetry; exact: measure_addE.
Qed.

Lemma run_if_expectation guard c1 c2 ps q : pstate_admissible ps ->
  expectation (pstate_measure (run (CIf guard c1 c2) ps)) (q_eval q) =
  (expectation (pstate_measure (run c1 (condition_state guard ps))) (q_eval q) +
   expectation (pstate_measure (run c2 (condition_state (c_not guard) ps))) (q_eval q))%R.
Proof.
  intro Hps; rewrite (expectation_measure_equiv _ _ _ (run_if_measure_equiv guard c1 c2 ps)).
  apply q_expectation_add; apply run_admissible; apply condition_state_admissible; exact Hps.
Qed.

(** SUM transforms both pieces with the same command. Input coverage and
    disjointness are used before applying command linearity; output supports
    may overlap completely. No termination premise is added. *)
Lemma run_sum_measure_equiv gamma delta c ps :
  cformula_valid (c_not (c_and gamma delta)) -> pstate_admissible ps ->
  psatisfies ps (p_almost_sure (c_or gamma delta)) ->
  measure_equiv (pstate_measure (run c ps))
    (ConcreteMeasure.add
      (pstate_measure (run c (condition_state gamma ps)))
      (pstate_measure (run c (condition_state delta ps)))).
Proof.
  move=> Hd Hps Hcover A mA.
  transitivity (transform_cmd c
    (ConcreteMeasure.add (pstate_measure (condition_state gamma ps))
      (pstate_measure (condition_state delta ps))) A).
  - apply transform_ext; [exact (sum_input_decomposition gamma delta ps Hd Hps Hcover)|exact mA].
  - transitivity
      (pstate_measure (run c (condition_state gamma ps)) A +
       pstate_measure (run c (condition_state delta ps)) A).
    + exact: cmd_add.
    + symmetry; exact: measure_addE.
Qed.

Lemma run_sum_expectation gamma delta c ps q :
  cformula_valid (c_not (c_and gamma delta)) -> pstate_admissible ps ->
  psatisfies ps (p_almost_sure (c_or gamma delta)) ->
  expectation (pstate_measure (run c ps)) (q_eval q) =
  (expectation (pstate_measure (run c (condition_state gamma ps))) (q_eval q) +
   expectation (pstate_measure (run c (condition_state delta ps))) (q_eval q))%R.
Proof.
  intros Hd Hps Hcover.
  rewrite (expectation_measure_equiv _ _ _ (run_sum_measure_equiv gamma delta c ps Hd Hps Hcover)).
  apply q_expectation_add; apply run_admissible; apply condition_state_admissible; exact Hps.
Qed.
