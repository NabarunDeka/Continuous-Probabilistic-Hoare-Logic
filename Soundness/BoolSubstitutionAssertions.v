(** Lift capture-avoiding Boolean substitution to probabilistic assertions.
    The joint measure is pushed through the Boolean update; rho is retained. *)
From Stdlib Require Import Reals.
Require Import MeasureIntegration CPHL Soundness.StateSpace Soundness.BindingFacts
  Soundness.RealSubstitutionAssertions.

Definition bool_substitution_state b beta (ps : Pstate) : Pstate :=
  {| pstate_measure := ConcreteMeasure.push (pstate_measure ps)
       (measurable_bool_assignment b beta);
     pstate_prob_logic_values := pstate_prob_logic_values ps |}.

Lemma bool_substitution_state_admissible b beta ps : pstate_admissible ps ->
  pstate_admissible (bool_substitution_state b beta ps).
Proof. apply ConcreteMeasure.push_subprob. Qed.

(** The local construct theorem includes binder collisions and replacements
    mentioning b. Pushforward integration evaluates beta once in the input. *)
Lemma subst_bool_expectation_correct b beta q mu :
  expectation mu (q_eval (subst_bool_pconstruct b beta q)) =
  expectation (ConcreteMeasure.push mu (measurable_bool_assignment b beta)) (q_eval q).
Proof.
  rewrite q_expectation_push.
  apply ConcreteMeasure.expectation_ext; intro v; apply subst_bool_pconstruct_correct.
Qed.

(** These are equalities of whole term values, so nonlinear arithmetic and
    implications are handled without any linearity assumption on assertions. *)
Lemma subst_bool_pterm_correct b beta p ps :
  pterm_eval (subst_bool_pterm b beta p) ps =
  pterm_eval p (bool_substitution_state b beta ps).
Proof.
  induction p; cbn [subst_bool_pterm pterm_eval bool_substitution_state
    pstate_measure pstate_prob_logic_values].
  - reflexivity.
  - reflexivity.
  - apply subst_bool_expectation_correct.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
Qed.

Lemma subst_bool_pformula_correct b beta eta ps :
  psatisfies ps (subst_bool_pformula b beta eta) <->
  psatisfies (bool_substitution_state b beta ps) eta.
Proof.
  induction eta; cbn [subst_bool_pformula psatisfies].
  - now rewrite !subst_bool_pterm_correct.
  - tauto.
  - tauto.
Qed.
