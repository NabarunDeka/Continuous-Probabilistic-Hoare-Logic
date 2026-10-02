(** Decompose admissible inputs into unnormalized restrictions. Coverage
    concerns the input measure; disjointness concerns the region predicates. *)
From Stdlib Require Import Reals.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals topology ereal measure.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From mathcomp Require Import lebesgue_stieltjes_measure Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.ConstructFacts Soundness.AssertionLogic
  Soundness.ConditioningAssertions.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Lemma formula_event_true : formula_event c_true = setT.
Proof.
  apply/funext => v; apply/propext.
  change ((False -> False) <-> True); tauto.
Qed.

Lemma formula_event_or gamma delta :
  formula_event (c_or gamma delta) = formula_event gamma `|` formula_event delta.
Proof.
  apply/funext => v; apply/propext.
  change (((satisfies v gamma -> False) -> satisfies v delta) <->
    (satisfies v gamma \/ satisfies v delta)).
  (** Only this syntactic event is decided when unpacking the encoded or. *)
  destruct (cformula_satisfies_dec gamma v); tauto.
Qed.

Lemma formula_events_disjoint gamma delta :
  cformula_valid (c_not (c_and gamma delta)) ->
  formula_event gamma `&` formula_event delta = set0.
Proof.
  move=> H; apply/funext => v; apply/propext.
  have Hv := H v; cbn [c_not c_and satisfies] in Hv.
  change ((satisfies v gamma /\ satisfies v delta) <-> False); tauto.
Qed.

(** Every restriction is concentrated on its own region, including zero
    restrictions. This does not require concentration of the original input. *)
Lemma condition_state_almost_sure gamma ps :
  psatisfies (condition_state gamma ps) (p_almost_sure gamma).
Proof.
  apply (proj2 (psatisfies_almost_sure _ _)); rewrite !expectation_indicator.
  rewrite -[formula_assertion c_true]/(formula_event c_true) formula_event_true.
  change (ConcreteMeasure.event_mass
    (ConcreteMeasure.restrict (pstate_measure ps) (measurable_formula_event gamma))
    (formula_event gamma) =
    ConcreteMeasure.event_mass
    (ConcreteMeasure.restrict (pstate_measure ps) (measurable_formula_event gamma)) setT).
  by rewrite /ConcreteMeasure.event_mass /ConcreteMeasure.restrict /= /mrestr setIid setTI.
Qed.

(** Equality of finite real masses makes the uncovered region null. A
    measurable subset of that region is null as well, giving event equality. *)
Lemma restriction_full_mass (mu : Measure) A (mA : measurable A) : Subprob mu ->
  ConcreteMeasure.event_mass mu A = ConcreteMeasure.event_mass mu setT ->
  measure_equiv (ConcreteMeasure.restrict mu mA) mu.
Proof.
  move=> Hmu Hmass.
  have Hfinite := ConcreteMeasure.subprob_finite Hmu.
  have Heq : mu A = mu setT.
  { by rewrite -(ConcreteMeasure.event_massE Hfinite mA)
      -(ConcreteMeasure.event_massE Hfinite measurableT) Hmass. }
  have Hnull : mu (~` A) = 0.
  { rewrite -setTD (measureD measurableT mA Hfinite) setTI.
    have Hfin := ConcreteMeasure.event_finite Hfinite measurableT.
    exact: eq_trans (congr1 (fun z => mu setT - z) Heq) (subee Hfin). }
  move=> B mB.
  have HB : mu (B `\` A) = 0.
  { apply: (@subset_measure0 _ _ _ mu (B `\` A) (~` A)
      (measurableD mB mA) (measurableC mA) _ Hnull).
    by move=> v [Hv Hnot]. }
  change (mu (B `&` A) = mu B).
  symmetry; transitivity (mu (B `\` A) + mu (B `&` A)).
  - exact: measureDI.
  - by rewrite HB add0e.
Qed.

Lemma almost_sure_restriction_equiv gamma ps : pstate_admissible ps ->
  psatisfies ps (p_almost_sure gamma) ->
  pstate_equiv (condition_state gamma ps) ps.
Proof.
  move=> Hps /psatisfies_almost_sure Hcover; split; last by move=> y.
  apply restriction_full_mass; first exact Hps.
  rewrite !expectation_indicator -[formula_assertion c_true]/(formula_event c_true)
    formula_event_true in Hcover; exact Hcover.
Qed.

(** Coverage may fail on a null set. First restrict to the covered union,
    then split that union using global disjointness of the two regions. *)
Lemma sum_input_decomposition gamma delta ps :
  cformula_valid (c_not (c_and gamma delta)) -> pstate_admissible ps ->
  psatisfies ps (p_almost_sure (c_or gamma delta)) ->
  measure_equiv (pstate_measure ps)
    (ConcreteMeasure.add (pstate_measure (condition_state gamma ps))
      (pstate_measure (condition_state delta ps))).
Proof.
  move=> Hd Hps Hcover.
  have [Hunion _] := almost_sure_restriction_equiv (c_or gamma delta) ps Hps Hcover.
  have Hdisj := formula_events_disjoint gamma delta Hd.
  move=> A mA.
  transitivity (
    pstate_measure ps (A `&` formula_event gamma) +
    pstate_measure ps (A `&` formula_event delta)).
  - rewrite -(Hunion A mA).
    change (pstate_measure ps (A `&` formula_event (c_or gamma delta)) =
      pstate_measure ps (A `&` formula_event gamma) +
      pstate_measure ps (A `&` formula_event delta)).
    rewrite formula_event_or setIUr.
    apply: measureU; try exact: measurableI mA (measurable_formula_event _).
    by rewrite setIACA setIid Hdisj setI0.
  - symmetry; exact: measure_addE.
Qed.

(** Integration adds outputs even when their supports overlap. Each input
    to this lemma is subprobabilistic; their sum need not have mass at most one. *)
Lemma q_expectation_add (mu nu : Measure) q : Subprob mu -> Subprob nu ->
  expectation (ConcreteMeasure.add mu nu) (q_eval q) =
  (expectation mu (q_eval q) + expectation nu (q_eval q))%R.
Proof.
  move=> Hmu Hnu.
  have mf : measurable_fun [set: Valuation] (fun v => (q_eval q v)%:E).
  { apply/measurable_EFinP; exact: q_eval_measurable. }
  have f0 v : 0 <= (q_eval q v)%:E by rewrite lee_fin; exact: q_eval_nonnegative.
  rewrite /expectation /ConcreteMeasure.expectation /Rintegral
    ge0_integral_measure_add //.
  rewrite -(q_expectation_extended q Hmu) -(q_expectation_extended q Hnu).
  by rewrite -EFinD.
Qed.
