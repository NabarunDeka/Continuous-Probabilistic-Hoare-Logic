(** General transformer laws apply to every Cmd because denote returns a
    subprobability kernel, including for loops. Input measures retain their
    ordinary carrier; only the theorems that need admissibility request it. *)
From Stdlib Require Import Reals.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import lebesgue_stieltjes_measure kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration DistributionKernels CPHL Soundness.CommandFacts
  Soundness.ConstructFacts Soundness.MeasureContinuity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Equality and order of measures are tested only on measurable events.
    No finite-mass hypothesis is needed for these nonnegative integral laws. *)
Lemma transform_ext k (mu nu : Measure) :
  (forall A, measurable A -> mu A = nu A) ->
  forall A, measurable A -> transform k mu A = transform k nu A.
Proof.
move=> h A mA; rewrite !transform_event.
by apply: eq_measure_integral => B mB _; exact: h.
Qed.
Lemma transform_monotone k mu nu : MeasureContinuity.below mu nu ->
  MeasureContinuity.below (transform k mu) (transform k nu).
Proof.
move=> h A mA; rewrite !transform_event.
apply: MeasureContinuity.integral_monotone => //; exact: measurable_kernel.
Qed.
Lemma transform_increasing k mus : MeasureContinuity.increasing mus ->
  MeasureContinuity.increasing (fun n => transform k (mus n)).
Proof. move=> h m n mn; apply: transform_monotone; exact: h mn. Qed.
Lemma transform_continuous k mus mu : MeasureContinuity.increasing mus ->
  MeasureContinuity.converges mus mu ->
  MeasureContinuity.converges (fun n => transform k (mus n)) (transform k mu).
Proof.
move=> hi hc A mA; rewrite !transform_event.
apply: MeasureContinuity.integral_increasing_cvg => //; exact: measurable_kernel.
Qed.
Lemma transform_series k mus A : measurable A ->
  transform k (ConcreteMeasure.series mus) A = \sum_(n <oo) transform k (mus n) A.
Proof.
move=> mA; rewrite !transform_event /ConcreteMeasure.series ge0_integral_measure_series//.
exact: measurable_kernel.
Qed.

(** The following statements expose the paper's T_c directly. Neither
    termination nor validity of every sampling parameter is a premise. *)
Lemma cmd_mass_nonincrease c mu : transform_cmd c mu setT <= mu setT.
Proof. exact: transform_mass_nonincrease. Qed.
Lemma cmd_subprob c mu : Subprob mu -> Subprob (transform_cmd c mu).
Proof. exact: transform_subprob. Qed.
Lemma run_admissible c ps : pstate_admissible ps -> pstate_admissible (run c ps).
Proof. exact: transform_pstate_admissible. Qed.
Lemma run_external c ps :
  pstate_prob_logic_values (run c ps) = pstate_prob_logic_values ps.
Proof. reflexivity. Qed.
Lemma run_measure c ps : pstate_measure (run c ps) = transform_cmd c (pstate_measure ps).
Proof. reflexivity. Qed.
Lemma cmd_zero c A : transform_cmd c mzero A = 0.
Proof. exact: transform_zero. Qed.
Lemma cmd_point c v A : measurable A -> transform_cmd c (dirac v) A = denote c v A.
Proof. exact: transform_point. Qed.
Lemma cmd_add c mu nu A : measurable A ->
  transform_cmd c (measure_add mu nu) A = transform_cmd c mu A + transform_cmd c nu A.
Proof. exact: transform_add. Qed.
Lemma cmd_scale c (a : {nonneg real}) mu A : measurable A ->
  transform_cmd c (mscale a mu) A = a%:num%:E * transform_cmd c mu A.
Proof. exact: transform_scale. Qed.

(** Arbitrary nonnegative coefficients are allowed in the linearity law.
    Admissibility of a weighted input remains a separate mass-budget premise. *)
Lemma cmd_linear c (a b : {nonneg real}) mu nu A : measurable A ->
  transform_cmd c (measure_add (mscale a mu) (mscale b nu)) A =
    a%:num%:E * transform_cmd c mu A + b%:num%:E * transform_cmd c nu A.
Proof.
move=> mA; rewrite cmd_add// (@cmd_scale c a mu A mA).
by rewrite [in X in _ + X](@cmd_scale c b nu A mA).
Qed.
Lemma cmd_monotone c mu nu : MeasureContinuity.below mu nu ->
  MeasureContinuity.below (transform_cmd c mu) (transform_cmd c nu).
Proof. exact: transform_monotone. Qed.
Lemma cmd_increasing c mus : MeasureContinuity.increasing mus ->
  MeasureContinuity.increasing (fun n => transform_cmd c (mus n)).
Proof. exact: transform_increasing. Qed.
Lemma cmd_continuous c mus mu : MeasureContinuity.increasing mus ->
  MeasureContinuity.converges mus mu ->
  MeasureContinuity.converges (fun n => transform_cmd c (mus n)) (transform_cmd c mu).
Proof. exact: transform_continuous. Qed.
Lemma cmd_series c mus A : measurable A ->
  transform_cmd c (ConcreteMeasure.series mus) A = \sum_(n <oo) transform_cmd c (mus n) A.
Proof. exact: transform_series. Qed.

(** Finite sums give a useful increasing approximation to any countable
    mixture, including mixtures whose components have overlapping support. *)
Lemma cmd_partial_sum_limit c mus :
  MeasureContinuity.converges
    (fun n => transform_cmd c (ConcreteMeasure.partial_sum mus n))
    (transform_cmd c (ConcreteMeasure.series mus)).
Proof.
apply: cmd_continuous.
- move=> m n hmn A _; exact: ConcreteMeasure.partial_sum_increasing hmn.
- move=> A _; exact: ConcreteMeasure.partial_sum_cvg.
Qed.

(** These analytic statements concern measures and integrals. They do not
    assert that arbitrary probabilistic formulas preserve limits or sums. *)
Lemma cmd_integral c mu f : Subprob mu ->
  (forall v, 0 <= f v) -> measurable_fun [set: Valuation] f ->
  \int[transform_cmd c mu]_w f w = \int[mu]_v (\int[denote c v]_w f w).
Proof. exact: transform_integral. Qed.
Lemma run_expectation_integrable c ps q : pstate_admissible ps ->
  expectation_integrable (pstate_measure (run c ps)) (q_eval q).
Proof. move=> hp; apply: q_expectation_integrable; exact: run_admissible. Qed.

(** The real projection is continuous here because the limiting expectation
    is finite. This applies to bounded constructs, not arbitrary formulas. *)
Lemma cmd_construct_expectation_cvg c mus mu q :
  MeasureContinuity.increasing mus -> MeasureContinuity.converges mus mu ->
  Subprob mu ->
  (fun n => expectation (transform_cmd c (mus n)) (q_eval q)) @ \oo -->
    expectation (transform_cmd c mu) (q_eval q).
Proof.
move=> hi hc hm.
have h0 : forall v, 0 <= (q_eval q v)%:E.
  by move=> v; rewrite lee_fin q_eval_nonnegative.
have mf : measurable_fun [set: Valuation] (fun v => (q_eval q v)%:E).
  apply/measurable_EFinP; exact: q_eval_measurable.
have hI := MeasureContinuity.integral_increasing_cvg
  (@cmd_increasing c mus hi) (@cmd_continuous c mus mu hi hc) h0 mf.
rewrite -(q_expectation_extended q (@cmd_subprob c mu hm)) in hI.
exact: fine_cvg hI.
Qed.
