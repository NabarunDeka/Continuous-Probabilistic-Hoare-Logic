(** Connect atomic command kernels to the assertion transformations. All
    integration steps use concrete bounded constructs, independently of rules. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology ereal measure.
From mathcomp Require Import measurable_realfun lebesgue_integral lebesgue_stieltjes_measure.
From mathcomp Require Import kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration DistributionKernels CPHL Soundness.StateSpace Soundness.BindingFacts
  Soundness.ConstructFacts Soundness.CommandFacts Soundness.AssertionLogic
  Soundness.RealSubstitutionAssertions Soundness.BoolSubstitutionAssertions.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** The kernel assignments agree with the substitution pushforwards on
    measurable events and preserve the same external assignment. *)
Lemma run_real_assign_equiv x t ps :
  pstate_equiv (run (CRealAssign x t) ps) (real_substitution_state x t ps).
Proof.
  split.
  - intros A HA; apply transform_deterministic; exact HA.
  - intro y; reflexivity.
Qed.

Lemma run_bool_assign_equiv b beta ps :
  pstate_equiv (run (CBoolAssign b beta) ps) (bool_substitution_state b beta ps).
Proof.
  split.
  - intros A HA; apply transform_deterministic; exact HA.
  - intro y; reflexivity.
Qed.

(** Translate the rule's real inequalities to the library's Boolean test. *)
Lemma coin_probability_valid_spec r :
  coin_probability_valid r <-> DistributionLaws.toss_valid r.
Proof.
  rewrite /coin_probability_valid /DistributionLaws.toss_valid.
  split.
  - move=> [h0 h1]; apply/andP; split; apply/RleP; assumption.
  - move=> /andP [/RleP h0 /RleP h1]; split; assumption.
Qed.

(** Each valid Bernoulli law evaluates q at the two updated states. Reusing
    Boolean substitution also accounts for integral binders inside q. *)
Lemma toss_q_eval b r q v : coin_probability_valid r ->
  ConcreteMeasure.expectation (CommandSemantics.toss b r v) (q_eval q) =
  (r * q_eval (subst_bool_pconstruct b c_true q) v +
    (1 - r) * q_eval (subst_bool_pconstruct b FFalse q) v)%R.
Proof.
  move=> hr.
  have hv := (proj1 (coin_probability_valid_spec r)) hr.
  have ht : cformula_eval_bool c_true v = true.
  { apply/cformula_eval_bool_spec; by []. }
  have hf : cformula_eval_bool FFalse v = false.
  { apply/negbTE; apply/negP => /cformula_eval_bool_spec; by []. }
  have f0 w : 0 <= (q_eval q w)%:E by rewrite lee_fin; exact: q_eval_nonnegative.
  have mf : measurable_fun [set: Valuation] (fun w => (q_eval q w)%:E).
  { apply/measurable_EFinP; exact: q_eval_measurable. }
  rewrite !subst_bool_pconstruct_correct ht hf.
  rewrite /ConcreteMeasure.expectation /Rintegral
    (@toss_integral_valid b r v (fun w => (q_eval q w)%:E) hv f0 mf).
  by rewrite -!EFinM -EFinD.
Qed.

(** Boundedness on subprobability input justifies real integral addition
    and scaling. We combine expectations before lifting through multiplication. *)
Lemma transform_toss_q_eval b r q mu : Subprob mu -> coin_probability_valid r ->
  expectation (transform [the real.-spker _ ~> _ of CommandSemantics.toss b r] mu)
    (q_eval q) =
  (r * expectation mu (q_eval (subst_bool_pconstruct b c_true q)) +
    (1 - r) * expectation mu (q_eval (subst_bool_pconstruct b FFalse q)))%R.
Proof.
  move=> hm hr.
  rewrite /expectation
    (@transform_expectation [the real.-spker _ ~> _ of CommandSemantics.toss b r]
      (q_eval q) (q_eval_measurable q) (q_eval_nonnegative q) (q_eval_le_one q) mu hm).
  transitivity (ConcreteMeasure.expectation mu (fun v =>
    (r * q_eval (subst_bool_pconstruct b c_true q) v +
      (1 - r) * q_eval (subst_bool_pconstruct b FFalse q) v)%R)).
  - apply ConcreteMeasure.expectation_ext; intro v; exact: toss_q_eval hr.
  - have ht := q_expectation_integrable (subst_bool_pconstruct b c_true q) hm.
    have hf := q_expectation_integrable (subst_bool_pconstruct b FFalse q) hm.
    have hts := ConcreteMeasure.integrable_scale r ht.
    have hfs := ConcreteMeasure.integrable_scale (1-r)%R hf.
    rewrite (ConcreteMeasure.expectation_add hts hfs).
    by rewrite (ConcreteMeasure.expectation_scale r ht)
      (ConcreteMeasure.expectation_scale (1-r)%R hf).
Qed.

Lemma toss_pterm_correct b r p ps :
  pstate_admissible ps -> coin_probability_valid r ->
  pterm_eval (toss_pterm b r p) ps = pterm_eval p (run (CBoolToss b r) ps).
Proof.
  intros Hps Hr; induction p; cbn [toss_pterm pterm_eval].
  - reflexivity.
  - reflexivity.
  - symmetry; apply transform_toss_q_eval; assumption.
  - now rewrite IHp1 IHp2.
  - now rewrite IHp1 IHp2.
Qed.

Lemma toss_pformula_correct b r eta ps :
  pstate_admissible ps -> coin_probability_valid r ->
  (psatisfies ps (toss_pformula b r eta) <-> psatisfies (run (CBoolToss b r) ps) eta).
Proof.
  intros Hps Hr; induction eta; cbn [toss_pformula psatisfies].
  - rewrite (toss_pterm_correct b r p1 ps Hps Hr)
      (toss_pterm_correct b r p2 ps Hps Hr); reflexivity.
  - tauto.
  - tauto.
Qed.

(** Sampling integrates against the law of the incoming state, including
    parameters mentioning x itself. The zero law for invalid parameters
    makes these identities valid without a parameter-validity premise. *)
Lemma sample_pterm_correct x d p ps : pstate_admissible ps ->
  pterm_eval (sample_pterm x d p) ps = pterm_eval p (run (CRealSample x d) ps).
Proof.
  intros Hps; induction p; cbn [sample_pterm pterm_eval].
  - reflexivity.
  - reflexivity.
  - symmetry; apply transform_sample_q_eval; exact Hps.
  - now rewrite IHp1 IHp2.
  - now rewrite IHp1 IHp2.
Qed.

Lemma sample_pformula_correct x d eta ps : pstate_admissible ps ->
  (psatisfies ps (sample_pformula x d eta) <-> psatisfies (run (CRealSample x d) ps) eta).
Proof.
  intros Hps; induction eta; cbn [sample_pformula psatisfies].
  - rewrite (sample_pterm_correct x d p1 ps Hps)
      (sample_pterm_correct x d p2 ps Hps); reflexivity.
  - tauto.
  - tauto.
Qed.
