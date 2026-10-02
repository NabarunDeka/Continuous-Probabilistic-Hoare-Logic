(** Finite exit rewards and their limit. Index zero includes non-entry;
    index n includes all exits after at most n completed body executions.
    Rewards are bounded constructs, not necessarily exit probabilities. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun measurable_realfun.
From mathcomp Require Import lebesgue_integral lebesgue_stieltjes_measure kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.ConstructFacts Soundness.CommandFacts
  Soundness.LoopFacts Soundness.MeasureContinuity Soundness.TransformerFacts
  Soundness.AssertionLogic Soundness.ConditioningAssertions Soundness.InputDecomposition.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Definition loop_exit_measure g k n mu : Measure :=
  ConcreteMeasure.restrict (loop_input g k n mu)
    (measurableC (measurable_formula_event g)).
Definition loop_exit_reward g k q n mu : R :=
  expectation (loop_input g k n mu) (q_eval (condition_pconstruct q (c_not g))).
Definition loop_reward_approx g k q n mu : R :=
  expectation (loop_output g k n mu) (q_eval q).

(** Admissibility follows from the already constructed exit kernels. It
    remains separate from the measure and is available even if the body loses mass. *)
Lemma loop_exit_measure_subprob g k n mu : Subprob mu ->
  Subprob (loop_exit_measure g k n mu).
Proof.
  move=> hm; apply: ConcreteMeasure.restrict_subprob; exact: loop_input_subprob.
Qed.

Lemma loop_output_subprob g k n mu : Subprob mu -> Subprob (loop_output g k n mu).
Proof.
  move=> hm; change (loop_output g k n mu setT <= 1).
  rewrite -(@transform_loop_approx g k n mu setT hm measurableT).
  exact: transform_subprob.
Qed.

Lemma loop_exit_rewardE g k q n mu :
  loop_exit_reward g k q n mu = expectation (loop_exit_measure g k n mu) (q_eval q).
Proof. apply condition_expectation_correct. Qed.

(** A reward is at most the mass of its own exit measure. Equality with
    exit mass is reserved for the constant-one construct. *)
Lemma loop_exit_reward_bounds g k q n mu : Subprob mu ->
  (0 <= loop_exit_reward g k q n mu <=
    measure_of (loop_exit_measure g k n mu) (fun _ => True))%R.
Proof.
  move=> hm; rewrite loop_exit_rewardE; apply/andP; split.
  - have /andP [h _] := q_expectation_bounds q (loop_exit_measure_subprob g k n mu hm).
    exact h.
  - exact: q_expectation_mass_bound (loop_exit_measure_subprob g k n mu hm).
Qed.

Lemma loop_exit_probability g k n mu :
  loop_exit_reward g k (QIndicator c_true) n mu =
    measure_of (loop_exit_measure g k n mu) (fun _ => True).
Proof.
  rewrite loop_exit_rewardE expectation_indicator.
  by rewrite -[formula_assertion c_true]/(formula_event c_true) formula_event_true.
Qed.

Lemma loop_reward_approx0 g k q mu :
  loop_reward_approx g k q 0 mu = loop_exit_reward g k q 0 mu.
Proof.
  rewrite loop_exit_rewardE; apply expectation_measure_equiv => A mA.
  exact: loop_output0.
Qed.

(** This sum concerns measures and expectations. Exit supports may overlap,
    and no analogous addition law for arbitrary assertions is assumed. *)
Lemma loop_reward_approxS g k q n mu : Subprob mu ->
  loop_reward_approx g k q n.+1 mu =
    (loop_reward_approx g k q n mu + loop_exit_reward g k q n.+1 mu)%R.
Proof.
  move=> hm.
  transitivity (expectation (ConcreteMeasure.add (loop_output g k n mu)
    (loop_exit_measure g k n.+1 mu)) (q_eval q)).
  - apply expectation_measure_equiv => A mA.
    transitivity (loop_output g k n mu A + loop_exit_measure g k n.+1 mu A).
    + exact: loop_outputS.
    + symmetry; exact: measure_addE.
  - rewrite (q_expectation_add _ _ q (loop_output_subprob g k n mu hm)
      (loop_exit_measure_subprob g k n.+1 mu hm)) -loop_exit_rewardE; reflexivity.
Qed.

Lemma loop_reward_approx_sum g k q n mu : Subprob mu ->
  loop_reward_approx g k q n mu = finite_r_sum n.+1 (fun i => loop_exit_reward g k q i mu).
Proof.
  move=> hm; elim: n => [|n ih].
  - rewrite loop_reward_approx0; cbn [finite_r_sum]; symmetry; exact: Rplus_0_l.
  - rewrite loop_reward_approxS // ih; reflexivity.
Qed.

Lemma loop_reward_approx_increasing g k q mu : Subprob mu ->
  nondecreasing_seq (fun n => loop_reward_approx g k q n mu).
Proof.
  move=> hm; apply/nondecreasing_seqP => n; rewrite loop_reward_approxS //.
  have /andP [h _] := loop_exit_reward_bounds g k q n.+1 mu hm.
  change ((loop_reward_approx g k q n mu <=
    loop_reward_approx g k q n mu + loop_exit_reward g k q n.+1 mu)%R).
  by rewrite lerDl.
Qed.

(** Removing the first completed step shifts every later exit. This
    recurrence is the finite-horizon interface for later while certificates. *)
Lemma loop_exit_reward_shift g k q n mu :
  loop_exit_reward g k q n.+1 mu = loop_exit_reward g k q n (loop_step g k mu).
Proof. by rewrite /loop_exit_reward loop_input_shift. Qed.

Lemma loop_reward_approx_unfold g k q n mu : Subprob mu ->
  loop_reward_approx g k q n.+1 mu =
    (loop_exit_reward g k q 0 mu + loop_reward_approx g k q n (loop_step g k mu))%R.
Proof.
  move=> hm.
  have hs : Subprob (loop_step g k mu).
  { apply: transform_subprob; exact: ConcreteMeasure.restrict_subprob. }
  elim: n => [|n ih].
  - by rewrite loop_reward_approxS // !loop_reward_approx0 loop_exit_reward_shift.
  - rewrite (loop_reward_approxS g k q n.+1 mu hm) ih
      (loop_reward_approxS g k q n (loop_step g k mu) hs) loop_exit_reward_shift.
    exact: Rplus_assoc.
Qed.

(** Exit reward plus still-guarded mass is bounded by initial mass. Missing
    body mass is allowed; the inequality does not assert termination. *)
Lemma loop_reward_accounting g k q n mu : Subprob mu ->
  (loop_reward_approx g k q n mu + measure_of (loop_input g k n mu) (formula_event g) <=
    measure_of mu (fun _ => True))%R.
Proof.
  move=> hm.
  have ho := loop_output_subprob g k n mu hm.
  have hi := @loop_input_subprob g k n mu hm.
  apply: (le_trans (y := (measure_of (loop_output g k n mu) (fun _ => True) +
    measure_of (loop_input g k n mu) (formula_event g))%R)).
  - exact: lerD (q_expectation_mass_bound q ho) (lexx _).
  rewrite -lee_fin EFinD /measure_of
    (ConcreteMeasure.event_massE (ConcreteMeasure.subprob_finite ho) measurableT)
    (ConcreteMeasure.event_massE (ConcreteMeasure.subprob_finite hi) (measurable_formula_event g))
    (ConcreteMeasure.event_massE (ConcreteMeasure.subprob_finite hm) measurableT).
  exact: loop_mass_accounting.
Qed.

(** Setwise increasing convergence of the finite exit measures lifts to
    nonnegative integrals. Finiteness of the loop output licenses the final
    projection to real rewards; no assertion is passed through a limit. *)
Lemma loop_reward_approx_cvg g k q mu : Subprob mu ->
  (fun n => loop_reward_approx g k q n mu) @ \oo -->
    expectation (transform [the real.-spker _ ~> _ of loop g k] mu) (q_eval q).
Proof.
  move=> hm.
  have hi : MeasureContinuity.increasing (fun n => loop_output g k n mu).
  { move=> m n hmn A mA; exact: loop_output_increasing hmn. }
  have hc : MeasureContinuity.converges (fun n => loop_output g k n mu)
    (transform [the real.-spker _ ~> _ of loop g k] mu).
  { move=> A mA; exact: loop_output_cvg. }
  have h0 v : 0 <= (q_eval q v)%:E by rewrite lee_fin; exact: q_eval_nonnegative.
  have mf : measurable_fun [set: Valuation] (fun v => (q_eval q v)%:E).
  { apply/measurable_EFinP; exact: q_eval_measurable. }
  have hI := MeasureContinuity.integral_increasing_cvg hi hc h0 mf.
  rewrite -(q_expectation_extended q (@transform_subprob _ mu hm)) in hI.
  exact: fine_cvg hI.
Qed.

(** The extended-real series has a finite value on admissible inputs. This
    explicitly identifies the reward sum with the actual loop denotation. *)
Lemma loop_reward_series g k q mu : Subprob mu ->
  (expectation (transform [the real.-spker _ ~> _ of loop g k] mu) (q_eval q))%:E =
    \sum_(n <oo) (loop_exit_reward g k q n mu)%:E.
Proof.
  move=> hm.
  have h0 v : 0 <= (q_eval q v)%:E by rewrite lee_fin; exact: q_eval_nonnegative.
  have mf : measurable_fun [set: Valuation] (fun v => (q_eval q v)%:E).
  { apply/measurable_EFinP; exact: q_eval_measurable. }
  rewrite (q_expectation_extended q (@transform_subprob _ mu hm)).
  transitivity (\int[ConcreteMeasure.series (fun n => loop_exit_measure g k n mu)]_v (q_eval q v)%:E).
  - apply: eq_measure_integral => A mA _.
    exact: transform_loop_series.
  - rewrite /ConcreteMeasure.series ge0_integral_measure_series //.
    apply: eq_eseriesr => n _; rewrite loop_exit_rewardE.
    symmetry; exact: q_expectation_extended (loop_exit_measure_subprob g k n mu hm).
Qed.

(** The final postcondition masks q by not-g. Every loop output already
    has this support, so the mask can be removed without assuming termination. *)
Lemma loop_output_conditioned_reward g k q mu : Subprob mu ->
  expectation (transform [the real.-spker _ ~> _ of loop g k] mu)
    (q_eval (condition_pconstruct q (c_not g))) =
  expectation (transform [the real.-spker _ ~> _ of loop g k] mu) (q_eval q).
Proof.
  move=> hm.
  have ho := @transform_subprob [the real.-spker _ ~> _ of loop g k] mu hm.
  have hz : measure_of (transform [the real.-spker _ ~> _ of loop g k] mu)
    (formula_event g) = 0%R.
  { by rewrite /measure_of /ConcreteMeasure.event_mass transform_loop_guard. }
  have hp := condition_expectation_partition q g _ ho.
  rewrite (condition_expectation_null q g _ ho hz) add0r in hp; symmetry; exact hp.
Qed.

(** Almost-sure exit support is relative to the surviving mass, including
    zero output. It says nothing about how much input mass terminates. *)
Lemma run_while_exit_support g body ps : pstate_admissible ps ->
  psatisfies (run (CWhile g body) ps) (p_almost_sure (c_not g)).
Proof.
  move=> hm; apply (proj2 (psatisfies_almost_sure _ _)).
  transitivity (expectation (pstate_measure (run (CWhile g body) ps))
    (q_eval (condition_pconstruct (QIndicator c_true) (c_not g)))).
  - apply ConcreteMeasure.expectation_ext => v.
    rewrite Conditioning.condition_pconstruct_correct.
    have -> : q_eval (QIndicator c_true) v = 1%R.
    { apply formula_indicator_true; cbn [c_true satisfies]; tauto. }
    (** The exit formula and the conditioning mask agree extensionally. *)
    rewrite q_eval_indicatorE; symmetry; exact: Rmult_1_r.
  - exact: loop_output_conditioned_reward.
Qed.

Lemma run_while_reward_cvg g body q ps : pstate_admissible ps ->
  (fun n => loop_reward_approx g (denote body) q n (pstate_measure ps)) @ \oo -->
    expectation (pstate_measure (run (CWhile g body) ps))
      (q_eval (condition_pconstruct q (c_not g))).
Proof.
  move=> hm; rewrite loop_output_conditioned_reward //; exact: loop_reward_approx_cvg.
Qed.
