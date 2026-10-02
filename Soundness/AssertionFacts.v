(** Semantic assertion facts over admissible probabilistic states. These do
    not assert soundness of an EPPL proof calculus or any Hoare rule. *)
From Stdlib Require Import Reals Lra.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets reals topology ereal measure.
From mathcomp Require Import lebesgue_stieltjes_measure Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.ConstructFacts.

Import numFieldTopology.Exports MeasurableR.
Open Scope R_scope.

(** Unpacking the record makes both quantifiers explicit. In particular rho
    is unrestricted, and the measure may correlate all classical coordinates. *)
Lemma pformula_valid_spec eta :
  pformula_valid eta <->
  forall (mu : Measure) (rho : ProbLogicVar -> R), Subprob mu ->
    psatisfies {| pstate_measure := mu; pstate_prob_logic_values := rho |} eta.
Proof.
  split.
  - intros H mu rho Hmu; apply H; exact Hmu.
  - intros H [mu rho] Hmu; apply H; exact Hmu.
Qed.

Lemma pformula_valid_at eta ps :
  pformula_valid eta -> pstate_admissible ps -> psatisfies ps eta.
Proof. intros Hvalid Hps; exact (Hvalid ps Hps). Qed.

(** CONSEQ can use semantic implication on an admissible state. Establishing
    command preservation of that premise remains the command-semantics task. *)
Lemma pformula_valid_implication eta xi ps :
  pformula_valid (PFImpl eta xi) -> pstate_admissible ps ->
  psatisfies ps eta -> psatisfies ps xi.
Proof. intros Hvalid Hps Heta; exact (Hvalid ps Hps Heta). Qed.

Lemma pformula_valid_modus_ponens eta xi :
  pformula_valid eta -> pformula_valid (PFImpl eta xi) -> pformula_valid xi.
Proof. intros Heta Himp ps Hps; exact (Himp ps Hps (Heta ps Hps)). Qed.

(** Every PExpect node denotes a finite integral. This is the analytical
    justification needed by the existing real arithmetic in pterm_eval. *)
Lemma pexpect_integrable q ps : pstate_admissible ps ->
  expectation_integrable (pstate_measure ps) (q_eval q).
Proof. intros Hps; apply q_expectation_integrable; exact Hps. Qed.

Lemma pexpect_bounds q ps : pstate_admissible ps ->
  Rle 0 (pterm_eval (PExpect q) ps) /\
  Rle (pterm_eval (PExpect q) ps) 1.
Proof.
  intros Hps.
  have /andP [/RleP H0 /RleP H1] := q_expectation_bounds q Hps.
  split; assumption.
Qed.

Lemma expectation_bound_valid q :
  pformula_valid
    (p_and (PFLe (PConst 0) (PExpect q))
      (PFLe (PExpect q) (PConst 1))).
Proof.
  intros ps Hps.
  pose proof (pexpect_bounds q ps Hps) as [H0 H1].
  cbn [p_and p_not psatisfies pterm_eval] in *; tauto.
Qed.

(** Almost-sure assertions compare event mass with total mass, so all such
    assertions hold on the zero measure without requiring normalization. *)
Example zero_almost_sure gamma rho :
  psatisfies
    {| pstate_measure := ConcreteMeasure.zero; pstate_prob_logic_values := rho |}
    (p_almost_sure gamma).
Proof.
  cbn [p_almost_sure p_eq p_and p_not psatisfies pterm_eval pstate_measure].
  rewrite !q_expectation_zero; lra.
Qed.

(** General probabilistic terms are not probabilities: constants and rho
    remain arbitrary real numbers, even on admissible states. *)
Example probabilistic_constant_above_one ps :
  1 < pterm_eval (PConst 2) ps.
Proof. cbn [pterm_eval]; lra. Qed.

Example probabilistic_constant_negative ps :
  pterm_eval (PConst (-1)) ps < 0.
Proof. cbn [pterm_eval]; lra. Qed.

Example external_assignment_unrestricted mu y r :
  pterm_eval (PVar y)
    {| pstate_measure := mu; pstate_prob_logic_values := fun _ => r |} = r.
Proof. reflexivity. Qed.
