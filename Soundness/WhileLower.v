(** Soundness of HWhileLower. Finite semantic rewards dominate the matrix
    rewards; progress removes the residual. Integration handles arbitrary
    concentrated joint inputs without dividing by their mass. *)
From Stdlib Require Import Reals Lra Lia.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals topology normedtype sequences.
From mathcomp Require Import measure lebesgue_stieltjes_measure kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.ConstructFacts Soundness.CommandFacts
  Soundness.AssertionLogic Soundness.ConditioningAssertions Soundness.InputDecomposition Soundness.RegionMeasureFacts
  Soundness.LowerRegions Soundness.LowerResidual Soundness.MatrixConvergence
  Soundness.WhileUpper Soundness.LowerLoopRewards.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Use a real point of the selected region to activate its row. No row
    bound is inferred for a region whose unit-mass premise is vacuous. *)
Theorem while_lower_point m g body q regions solution transitions exits :
  while_regions_in_guard m g regions -> while_regions_disjoint m regions ->
  while_progress m transitions exits ->
  (forall i, Nat.lt i m -> hoare_valid
    (p_concentrated_mass (regions i) (PConst R1)) body
    (while_body_post_lower m regions (transitions i) g q (exits i))) ->
  while_lower_solution m solution transitions exits ->
  forall i (v : Valuation), Nat.lt i m -> satisfies v (regions i) ->
  Rle (solution i) (expectation (denote (CWhile g body) v)
    (q_eval (condition_pconstruct q (c_not g)))).
Proof.
  move=> hg hd hp hb hs i v hi hv.
  apply (lower_certificate_reward_limit m g body q regions transitions exits
    hb hd hg hp solution hs i (fun n => finite_loop_value g (denote body) q n v)).
  - split; [exact hi|exists v; exact hv].
  - intro n; exact (finite_loop_value_lower m g body q regions transitions exits hd hg hb n i v hi hv).
  - apply (proj2 (real_sequence_cvg _ _)); exact: finite_loop_value_exit_cvg.
Qed.

(** The pointwise bound integrates over an almost-surely concentrated
    input. An empty selected region forces zero input, so its local bound
    is vacuous and its scaled conclusion still holds. Correlations between
    program and classical coordinates and arbitrary external values remain. *)
Theorem loop_reward_lower m k g body q regions solution transitions exits ps :
  Nat.lt k m -> while_regions_in_guard m g regions ->
  while_regions_disjoint m regions -> while_progress m transitions exits ->
  (forall i, Nat.lt i m -> hoare_valid
    (p_concentrated_mass (regions i) (PConst R1)) body
    (while_body_post_lower m regions (transitions i) g q (exits i))) ->
  while_lower_solution m solution transitions exits ->
  pstate_admissible ps -> psatisfies ps (p_almost_sure (regions k)) ->
  Rle (Rmult (solution k) (measure_of (pstate_measure ps) (fun _ => True)))
    (expectation (pstate_measure (run (CWhile g body) ps))
      (q_eval (condition_pconstruct q (c_not g)))).
Proof.
  move=> hk hg hd hprogress hb hs hp hreg.
  apply (concentrated_kernel_reward_lower (denote (CWhile g body)) (regions k)
    (condition_pconstruct q (c_not g)) (solution k) ps hp hreg).
  - exact (proj1 (proj2 (hs k hk))).
  - intros v hv; exact (while_lower_point m g body q regions solution transitions exits
      hg hd hprogress hb hs k v hk hv).
Qed.

(** This is the declared HWhileLower contract with semantic validity for
    the recursive body premises. The lower mass bound may be negative;
    nonnegativity of the solution is all that its final multiplication needs. *)
Theorem hoare_valid_while_lower m k g body q regions solution transitions exits y :
  Nat.lt k m -> while_regions_in_guard m g regions ->
  while_regions_disjoint m regions -> while_progress m transitions exits ->
  (forall i, Nat.lt i m -> hoare_valid
    (p_concentrated_mass (regions i) (PConst R1)) body
    (while_body_post_lower m regions (transitions i) g q (exits i))) ->
  while_lower_solution m solution transitions exits ->
  hoare_valid (p_concentrated_mass_lower (regions k) (PVar y)) (CWhile g body)
    (PFLe (PMul (PConst (solution k)) (PVar y))
      (PExpect (condition_pconstruct q (c_not g)))).
Proof.
  move=> hk hg hd hprogress hb hs ps hp /psatisfies_and [hreg hmass].
  have hbound := loop_reward_lower m k g body q regions solution transitions exits ps
    hk hg hd hprogress hb hs hp hreg.
  change (Rle (pstate_prob_logic_values ps y)
    (expectation (pstate_measure ps) (q_eval (QIndicator c_true)))) in hmass.
  rewrite expectation_indicator -[formula_assertion c_true]/(formula_event c_true) formula_event_true in hmass.
  change (Rle (Rmult (solution k) (pstate_prob_logic_values ps y))
    (expectation (pstate_measure (run (CWhile g body) ps)) (q_eval (condition_pconstruct q (c_not g))))).
  eapply Rle_trans; last exact hbound.
  apply Rmult_le_compat_l; [exact (proj1 (proj2 (hs k hk)))|exact hmass].
Qed.
