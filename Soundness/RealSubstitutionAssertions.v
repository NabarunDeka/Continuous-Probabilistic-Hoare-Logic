(** Lift real substitution through a measurable pushforward, then through
    probabilistic arithmetic and assertions. The assignment rule itself is
    left to the atomic-rule task. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals topology ereal measure.
From mathcomp Require Import measurable_realfun lebesgue_integral lebesgue_stieltjes_measure Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.StateSpace Soundness.ConstructFacts
  Soundness.RealSubstitution.

Import numFieldTopology.Exports MeasurableR ValuationSpace.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Nonnegative pushforward integration works for any input measure. The
    total real projections therefore agree as well. On admissible inputs,
    the existing construct bounds separately ensure finite expectations. *)
Lemma q_expectation_push (mu : Measure) (phi : Valuation -> Valuation)
    (mphi : measurable_fun setT phi) q :
  expectation (ConcreteMeasure.push mu mphi) (q_eval q) =
  expectation mu (fun v => q_eval q (phi v)).
Proof.
  unfold expectation, ConcreteMeasure.expectation, Rintegral.
  f_equal; apply ConcreteMeasure.integral_push.
  - apply/measurable_EFinP; exact: q_eval_measurable.
  - intro v; rewrite lee_fin; exact: q_eval_nonnegative.
Qed.

(** Only the joint measure is pushed forward; rho and the logic coordinates
    inside each valuation are preserved. Correlation is unrestricted. *)
Definition real_substitution_state x t (ps : Pstate) : Pstate :=
  {| pstate_measure := ConcreteMeasure.push (pstate_measure ps)
       (measurable_real_assignment x t);
     pstate_prob_logic_values := pstate_prob_logic_values ps |}.

Lemma real_substitution_state_admissible x t ps : pstate_admissible ps ->
  pstate_admissible (real_substitution_state x t ps).
Proof. exact: ConcreteMeasure.push_subprob. Qed.

Lemma subst_real_expectation_correct x t q mu :
  expectation mu (q_eval (subst_real_pconstruct x t q)) =
  expectation (ConcreteMeasure.push mu (measurable_real_assignment x t)) (q_eval q).
Proof.
  rewrite q_expectation_push.
  apply ConcreteMeasure.expectation_ext; intro v; apply subst_real_pconstruct_correct.
Qed.

(** Multiplication is handled by equality of each term's value, not by a
    linearity claim for arbitrary probabilistic terms or formulas. *)
Lemma subst_real_pterm_correct x t p ps :
  pterm_eval (subst_real_pterm x t p) ps =
  pterm_eval p (real_substitution_state x t ps).
Proof.
  induction p; cbn [subst_real_pterm pterm_eval real_substitution_state
    pstate_measure pstate_prob_logic_values].
  - reflexivity.
  - reflexivity.
  - apply subst_real_expectation_correct.
  - now rewrite IHp1 IHp2.
  - now rewrite IHp1 IHp2.
Qed.

Lemma subst_real_pformula_correct x t eta ps :
  psatisfies ps (subst_real_pformula x t eta) <->
  psatisfies (real_substitution_state x t ps) eta.
Proof.
  induction eta; cbn [subst_real_pformula psatisfies].
  - now rewrite !subst_real_pterm_correct.
  - tauto.
  - tauto.
Qed.
