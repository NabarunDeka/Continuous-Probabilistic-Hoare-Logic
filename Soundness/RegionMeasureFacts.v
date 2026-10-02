(** Measure facts for lower while certificates. Disjoint guarded regions
    account for only part of the output; missing mass and body divergence
    are allowed. All real integrations below have proved integrability. *)
From Stdlib Require Import Reals Lra Lia.
From mathcomp Require Import boot order ssralg ssrnum.
From mathcomp Require Import boolp classical_sets functions reals topology ereal measure.
From mathcomp Require Import numfun measurable_realfun lebesgue_integral.
From mathcomp Require Import lebesgue_stieltjes_measure kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.ConstructFacts Soundness.CommandFacts
  Soundness.TransformerFacts Soundness.AssertionLogic Soundness.Conditioning
  Soundness.ConditioningAssertions Soundness.InputDecomposition Soundness.FiniteExpectationBounds.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Lemma finite_r_sum_ext m f h : (forall i, Nat.lt i m -> f i = h i) ->
  finite_r_sum m f = finite_r_sum m h.
Proof.
  induction m as [|m ih]; intro he; cbn [finite_r_sum]; first reflexivity.
  apply (f_equal2 Rplus); [apply ih; intros; apply he; lia|apply he; lia].
Qed.

Lemma finite_r_sum_zero m f : (forall i, Nat.lt i m -> f i = R0) ->
  finite_r_sum m f = R0.
Proof.
  induction m as [|m ih]; intro hz; cbn [finite_r_sum]; first reflexivity.
  have hp : finite_r_sum m f = R0 by apply ih; intros; apply hz; lia.
  have hm : f m = R0 by apply hz; lia.
  rewrite hp hm; exact: Rplus_0_l.
Qed.

(** At most one region can contain a valuation. Thus its finite indicator
    sum is exactly the indicator of the union, even without guard coverage. *)
Lemma disjoint_region_indicator_sum m regions v : while_regions_disjoint m regions ->
  finite_r_sum m (fun i => q_eval (QIndicator (regions i)) v) =
  q_eval (QIndicator (finite_c_or m regions)) v.
Proof.
  induction m as [|m ih]; intro hd.
  - symmetry; apply formula_indicator_false; tauto.
  - have hp : while_regions_disjoint m regions by intros i j hi hj; apply hd; lia.
    cbn [finite_r_sum]; rewrite (ih hp).
    have hdis : ~ (satisfies v (finite_c_or m regions) /\ satisfies v (regions m)).
    { intros [hu hm]; have [j [hj hv] ] := proj1 (satisfies_finite_c_or m regions v) hu.
      have hh := hd m j (Nat.lt_succ_diag_r m) hj v.
      cbn [c_not c_and satisfies] in hh; tauto. }
    have hor : satisfies v (finite_c_or m.+1 regions) <->
      satisfies v (finite_c_or m regions) \/ satisfies v (regions m).
    { cbn [finite_c_or c_or c_not satisfies].
      destruct (cformula_satisfies_dec (finite_c_or m regions) v); tauto. }
    (** Bridge syntax indicators to the unchanged real mask arithmetic. *)
    rewrite !q_eval_indicatorE.
    change (Rplus (real_indicator (satisfies v (finite_c_or m regions)))
      (real_indicator (satisfies v (regions m))) =
      real_indicator (satisfies v (finite_c_or m.+1 regions))).
    rewrite (real_indicator_extensional _ _ hor).
    destruct (cformula_satisfies_dec (finite_c_or m regions) v) as [hu|hu];
      destruct (cformula_satisfies_dec (regions m) v) as [hm|hm];
      try solve [exfalso; apply hdis; split; assumption].
    + rewrite (real_indicator_true _ hu) (real_indicator_false _ hm)
        (real_indicator_true _ (or_introl hu)); lra.
    + rewrite (real_indicator_false _ hu) (real_indicator_true _ hm)
        (real_indicator_true _ (or_intror hm)); lra.
    + have hn : ~ (satisfies v (finite_c_or m regions) \/ satisfies v (regions m)) by tauto.
      rewrite (real_indicator_false _ hu) (real_indicator_false _ hm) (real_indicator_false _ hn); lra.
Qed.

(** Stdlib-facing kernel bounds keep finite coefficient algebra independent
    of the library's Boolean order notation. *)
Lemma kernel_reward_bounds (k : Kernel) q v :
  Rle R0 (expectation (k v) (q_eval q)) /\ Rle (expectation (k v) (q_eval q)) R1.
Proof.
  have /andP [/RleP h0 /RleP h1] := q_expectation_bounds q (sprob_kernel_le1 k v).
  split; assumption.
Qed.

Lemma disjoint_region_reward_bound m g regions q v :
  while_regions_disjoint m regions -> while_regions_in_guard m g regions ->
  Rle (Rplus (finite_r_sum m (fun i => q_eval (QIndicator (regions i)) v))
    (q_eval (condition_pconstruct q (c_not g)) v)) R1.
Proof.
  move=> hd hg; rewrite (disjoint_region_indicator_sum m regions v hd).
  destruct (cformula_satisfies_dec (finite_c_or m regions) v) as [hu|hu].
  - have [i [hi hv] ] := proj1 (satisfies_finite_c_or m regions v) hu.
    have hvguard := hg i hi v hv.
    have hn : ~ satisfies v (c_not g) by cbn [c_not satisfies]; tauto.
    rewrite condition_pconstruct_correct (real_indicator_false _ hn).
    rewrite q_eval_indicatorE.
    change (Rle (Rplus (real_indicator (satisfies v (finite_c_or m regions)))
      (Rmult R0 (q_eval q v))) R1).
    rewrite (real_indicator_true _ hu); lra.
  - have he : q_eval (QIndicator (finite_c_or m regions)) v = R0 by apply formula_indicator_false.
    rewrite he; have h := proj2 (q_eval_bounds_real (condition_pconstruct q (c_not g)) v); lra.
Qed.

(** Continuing regional mass plus exit reward is bounded by total mass.
    The reward can be smaller than exit probability; no equality is claimed. *)
Lemma region_reward_budget m g regions q (mu : Measure) : Subprob mu ->
  while_regions_disjoint m regions -> while_regions_in_guard m g regions ->
  Rle (Rplus (finite_r_sum m (fun i => expectation mu (q_eval (QIndicator (regions i)))))
    (expectation mu (q_eval (condition_pconstruct q (c_not g)))))
    (measure_of mu (fun _ => True)).
Proof.
  move=> hm hd hg.
  have hi i : ConcreteMeasure.Integrable mu (q_eval (QIndicator (regions i)))
    by exact: q_expectation_integrable.
  have hs := integrable_finite_r_sum mu m _ (fun i _ => hi i).
  have hr := q_expectation_integrable (condition_pconstruct q (c_not g)) hm.
  have ht := q_expectation_integrable (QIndicator c_true) hm.
  have hbound := expectation_le_integrable mu _ _ (ConcreteMeasure.integrable_add hs hr) ht.
  have hpoint v : Rle
    (Rplus (finite_r_sum m (fun i => q_eval (QIndicator (regions i)) v))
      (q_eval (condition_pconstruct q (c_not g)) v)) (q_eval (QIndicator c_true) v).
  { have he : q_eval (QIndicator c_true) v = R1 by apply formula_indicator_true; cbn [c_true satisfies]; tauto.
    rewrite he; exact (disjoint_region_reward_bound m g regions q v hd hg). }
  have hb := hbound hpoint.
  rewrite /expectation (ConcreteMeasure.expectation_add hs hr) in hb.
  change (Rle (Rplus
    (expectation mu (fun v => finite_r_sum m (fun i => q_eval (QIndicator (regions i)) v)))
    (expectation mu (q_eval (condition_pconstruct q (c_not g)))))
    (expectation mu (q_eval (QIndicator c_true)))) in hb.
  rewrite (expectation_finite_r_sum mu m _ (fun i _ => hi i)) expectation_indicator
    -[formula_assertion c_true]/(formula_event c_true) formula_event_true in hb; exact hb.
Qed.

Lemma kernel_region_reward_budget m g regions q (k : Kernel) v :
  while_regions_disjoint m regions -> while_regions_in_guard m g regions ->
  Rle (Rplus (finite_r_sum m (fun i => expectation (k v) (q_eval (QIndicator (regions i)))))
    (expectation (k v) (q_eval (condition_pconstruct q (c_not g))))) R1.
Proof.
  move=> hd hg; have hm : Subprob (k v) by exact: sprob_kernel_le1.
  eapply Rle_trans; first exact (region_reward_budget m g regions q _ hm hd hg).
  exact (elimT RleP (ConcreteMeasure.mass_bound hm)).
Qed.

Lemma empty_region_expectation (mu : Measure) gamma :
  (forall v, ~ satisfies v gamma) -> expectation mu (q_eval (QIndicator gamma)) = R0.
Proof.
  intro he; transitivity (expectation mu (fun _ => R0)); last exact: ConcreteMeasure.expectation_zero.
  apply ConcreteMeasure.expectation_ext => v; apply formula_indicator_false; exact: he.
Qed.

(** Finiteness is essential when inferring a zero measure from its real
    mass. Subprobability supplies it; infinite mass is never projected here. *)
Lemma zero_mass_measure_equiv (mu : Measure) : Subprob mu ->
  measure_of mu (fun _ => True) = R0 -> measure_equiv mu ConcreteMeasure.zero.
Proof.
  move=> hm hz.
  have hT : mu setT = 0.
  { rewrite -(ConcreteMeasure.event_massE (ConcreteMeasure.subprob_finite hm) measurableT).
    change ((measure_of mu (fun _ => True))%:E = 0); by rewrite hz. }
  move=> A mA; exact: subset_measure0 mA measurableT (subsetT A) hT.
Qed.

Lemma concentrated_empty_zero gamma ps : (forall v, ~ satisfies v gamma) ->
  pstate_admissible ps -> psatisfies ps (p_almost_sure gamma) ->
  measure_equiv (pstate_measure ps) ConcreteMeasure.zero.
Proof.
  move=> he hp /psatisfies_almost_sure hs; apply zero_mass_measure_equiv; first exact hp.
  rewrite (empty_region_expectation _ gamma he) expectation_indicator
    -[formula_assertion c_true]/(formula_event c_true) formula_event_true in hs.
  symmetry; exact hs.
Qed.

Lemma zero_mass_command_expectation c ps q : pstate_admissible ps ->
  measure_of (pstate_measure ps) (fun _ => True) = R0 ->
  expectation (pstate_measure (run c ps)) (q_eval q) = R0.
Proof.
  move=> hp hz; transitivity (expectation (ConcreteMeasure.zero : Measure) (q_eval q));
    last exact: q_expectation_zero.
  apply expectation_measure_equiv => A mA.
  transitivity (transform_cmd c ConcreteMeasure.zero A); last exact: cmd_zero.
  apply transform_ext; [exact (zero_mass_measure_equiv _ hp hz)|exact mA].
Qed.

(** A local lower bound integrates on a restriction without division.
    Thus the subsequent concentrated-input lemma includes zero input mass. *)
Lemma expectation_restrict_lower_bound (mu : Measure) gamma (f : Valuation -> real) a :
  Subprob mu -> measurable_fun setT f ->
  (forall v, (0 <= f v)%R) -> (forall v, (f v <= 1)%R) ->
  (0 <= a)%R -> (forall v, satisfies v gamma -> (a <= f v)%R) ->
  (a * measure_of mu (formula_event gamma) <=
    expectation (ConcreteMeasure.restrict mu (measurable_formula_event gamma)) f)%R.
Proof.
  move=> hm mf f0 f1 a0 haf.
  have hr : Subprob (ConcreteMeasure.restrict mu (measurable_formula_event gamma))
    by exact: ConcreteMeasure.restrict_subprob.
  have hI := ConcreteMeasure.bounded_integrable hr mf f0 f1.
  have mfE : measurable_fun setT (fun v => (f v)%:E) by exact/measurable_EFinP.
  have fE0 v : 0 <= (f v)%:E by rewrite lee_fin.
  rewrite -lee_fin (ConcreteMeasure.expectationE hI) EFinM /measure_of
    (ConcreteMeasure.event_massE (ConcreteMeasure.subprob_finite hm) (measurable_formula_event gamma)).
  rewrite -/(ConcreteMeasure.integral _ _)
    (ConcreteMeasure.integral_restrict mu (measurable_formula_event gamma) mfE fE0).
  rewrite /ConcreteMeasure.integral -integral_mkcond -integral_cst //;
    first exact: measurable_formula_event.
  apply: ge0_le_integral => //.
  - exact: measurable_formula_event.
  - exact: measurable_funS mfE.
Qed.

Lemma concentrated_kernel_reward_lower (k : Kernel) gamma q a ps :
  pstate_admissible ps -> psatisfies ps (p_almost_sure gamma) -> Rle R0 a ->
  (forall (v : Valuation), satisfies v gamma ->
    Rle a (expectation (k v) (q_eval q))) ->
  Rle (Rmult a (measure_of (pstate_measure ps) (fun _ => True)))
    (expectation (transform k (pstate_measure ps)) (q_eval q)).
Proof.
  move=> hp hreg ha hpoint.
  have [he _] := almost_sure_restriction_equiv gamma ps hp hreg.
  have hmass : measure_of (pstate_measure ps) (formula_event gamma) =
    measure_of (pstate_measure ps) (fun _ => True).
  { rewrite -restriction_formula_mass /measure_of /ConcreteMeasure.event_mass (he setT measurableT); reflexivity. }
  rewrite /expectation (@transform_expectation k (q_eval q) (q_eval_measurable q)
    (q_eval_nonnegative q) (q_eval_le_one q) _ hp).
  change (Rle (Rmult a (measure_of (pstate_measure ps) (fun _ => True)))
    (expectation (pstate_measure ps) (kernel_expectation k (q_eval q)))).
  rewrite -(expectation_measure_equiv _ _ _ he) -hmass.
  apply/RleP; apply (expectation_restrict_lower_bound _ gamma _ a hp).
  - exact (@kernel_expectation_measurable k (q_eval q) (q_eval_measurable q) (q_eval_nonnegative q)).
  - move=> v; exact (proj1 (andP (q_expectation_bounds q (sprob_kernel_le1 k v)))).
  - move=> v; exact (proj2 (andP (q_expectation_bounds q (sprob_kernel_le1 k v)))).
  - exact/RleP/ha.
  - move=> v hv; exact/RleP/hpoint.
Qed.

(** Every nonempty region has a unit point input. Extract the actual kernel
    bounds there; do not infer any coefficient bounds on an empty source. *)
Lemma while_lower_body_point m g body q regions transitions exits :
  (forall i, Nat.lt i m -> hoare_valid
    (p_concentrated_mass (regions i) (PConst R1)) body
    (while_body_post_lower m regions (transitions i) g q (exits i))) ->
  forall i (v : Valuation), Nat.lt i m -> satisfies v (regions i) ->
  (forall j, Nat.lt j m -> Rle (transitions i j)
    (expectation (denote body v) (q_eval (QIndicator (regions j))))) /\
  Rle (exits i) (expectation (denote body v) (q_eval (condition_pconstruct q (c_not g)))).
Proof.
  move=> hb i v hi hv.
  set ps := {| pstate_measure := ConcreteMeasure.point v;
    pstate_prob_logic_values := fun _ => R0 |}.
  have hp : psatisfies ps (p_concentrated_mass (regions i) (PConst R1)).
  { rewrite /p_concentrated_mass psatisfies_and !psatisfies_eq; cbn [pterm_eval ps pstate_measure].
    rewrite !q_expectation_point.
    have ht : q_eval (QIndicator c_true) v = R1 by apply formula_indicator_true; cbn [c_true satisfies]; tauto.
    have hc : q_eval (QIndicator (regions i)) v = R1 by apply formula_indicator_true.
    by rewrite ht hc. }
  have hout := hb i hi ps (ConcreteMeasure.point_subprob v) hp.
  rewrite /while_body_post_lower psatisfies_and psatisfies_finite_p_and in hout.
  have he q' : expectation (pstate_measure (run body ps)) (q_eval q') =
    expectation (denote body v) (q_eval q').
  { apply expectation_measure_equiv => A mA; exact: transform_point. }
  destruct hout as [ht hx]; split.
  - move=> j hj; have h := ht j hj; change (Rle (transitions i j)
      (expectation (pstate_measure (run body ps)) (q_eval (QIndicator (regions j))))) in h; by rewrite he in h.
  - change (Rle (exits i) (expectation (pstate_measure (run body ps))
      (q_eval (condition_pconstruct q (c_not g))))) in hx; by rewrite he in hx.
Qed.
