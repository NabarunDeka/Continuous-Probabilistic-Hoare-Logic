(** Non-entry preserves the entire input state, not only its total mass.
    This proves HWhileNot for arbitrary admissible mass and external values. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals topology ereal measure.
From mathcomp Require Import lebesgue_integral lebesgue_stieltjes_measure kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.CommandFacts Soundness.LoopFacts
  Soundness.TransformerFacts Soundness.AssertionLogic Soundness.ConditioningAssertions
  Soundness.InputDecomposition.

Import numFieldTopology.Exports MeasurableR ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** On an explicitly restricted input every remaining valuation fails the
    guard. The body is never invoked; its behavior and termination are irrelevant. *)
Lemma loop_restricted_nonentry gamma g k mu :
  cformula_valid (FImpl gamma (c_not g)) ->
  measure_equiv
    (transform [the real.-spker _ ~> _ of loop g k]
      (ConcreteMeasure.restrict mu (measurable_formula_event gamma)))
    (ConcreteMeasure.restrict mu (measurable_formula_event gamma)).
Proof.
  move=> H A mA.
  transitivity (transform [the real.-spker _ ~> _ of CommandSemantics.skip]
    (ConcreteMeasure.restrict mu (measurable_formula_event gamma)) A); last exact: transform_skip.
  rewrite !transform_event -!/(ConcreteMeasure.integral _ _) !ConcreteMeasure.integral_restrict //;
    try exact: measurable_kernel.
  rewrite /ConcreteMeasure.integral.
  apply: eq_integral => v _; rewrite /patch.
  case: ifP => hv; last reflexivity.
  apply: loop_nonentry => //.
  apply/negbTE; apply/negP => /cformula_eval_bool_spec hg.
  exact: (H v (set_mem hv) hg).
Qed.

(** Almost-sure concentration suffices: null exceptional valuations do not
    contribute to the kernel integral. The proof never divides by input mass. *)
Lemma run_while_nonentry_equiv gamma g body ps :
  cformula_valid (FImpl gamma (c_not g)) -> pstate_admissible ps ->
  psatisfies ps (p_almost_sure gamma) -> pstate_equiv (run (CWhile g body) ps) ps.
Proof.
  move=> H Hps Hgamma.
  have [Hmu Hrho] := almost_sure_restriction_equiv gamma ps Hps Hgamma.
  split; last by move=> y.
  move=> A mA.
  transitivity (transform_cmd (CWhile g body) (pstate_measure (condition_state gamma ps)) A).
  - apply transform_ext; [apply measure_equiv_sym; exact Hmu|exact mA].
  - transitivity (pstate_measure (condition_state gamma ps) A).
    + exact (loop_restricted_nonentry gamma g (denote body) (pstate_measure ps) H A mA).
    + exact: Hmu.
Qed.

(** All assertions, including nonlinear terms and implications, are retained
    under non-entry because both the measure and external assignment agree. *)
Lemma hoare_valid_while_nonentry gamma g body eta :
  cformula_valid (FImpl gamma (c_not g)) ->
  hoare_valid (p_and eta (p_almost_sure gamma)) (CWhile g body) eta.
Proof.
  move=> H ps Hps /psatisfies_and [Heta Hgamma].
  apply (proj2 (psatisfies_equiv eta _ _ (run_while_nonentry_equiv gamma g body ps H Hps Hgamma))).
  exact Heta.
Qed.

(** This more general helper allows any mass term. The declared rule below
    instantiates it with PVar y, and the existing unit rule with PConst 1. *)
Lemma hoare_valid_while_nonentry_mass gamma g body mass :
  cformula_valid (FImpl gamma (c_not g)) ->
  hoare_valid (p_concentrated_mass gamma mass) (CWhile g body)
    (p_concentrated_mass gamma mass).
Proof.
  move=> H ps Hps Hpre.
  have Hgamma : psatisfies ps (p_almost_sure gamma).
  { exact (proj1 (proj1 (psatisfies_and _ _ _) Hpre)). }
  apply (proj2 (psatisfies_equiv _ _ _ (run_while_nonentry_equiv gamma g body ps H Hps Hgamma))).
  exact Hpre.
Qed.

Theorem hoare_valid_while_not gamma beta body y :
  cformula_valid (FImpl gamma (c_not beta)) ->
  hoare_valid (p_concentrated_mass gamma (PVar y)) (CWhile beta body)
    (p_concentrated_mass gamma (PVar y)).
Proof. apply hoare_valid_while_nonentry_mass. Qed.

Lemma hoare_valid_while_not_unit gamma beta body :
  cformula_valid (FImpl gamma (c_not beta)) ->
  hoare_valid (p_concentrated_mass gamma (PConst 1%R)) (CWhile beta body)
    (p_concentrated_mass gamma (PConst 1%R)).
Proof. apply hoare_valid_while_nonentry_mass. Qed.
