(** Finite lower certificates undercount the actual loop reward. Regions
    must be disjoint and guarded, but need not cover the guard. *)
From Stdlib Require Import Reals Lra Lia.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences measure numfun measurable_realfun.
From mathcomp Require Import lebesgue_integral lebesgue_stieltjes_measure kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.ConstructFacts Soundness.CommandFacts
  Soundness.LoopFacts Soundness.TransformerFacts Soundness.AssertionLogic
  Soundness.Conditioning Soundness.LoopRewards Soundness.FiniteExpectationBounds
  Soundness.RegionMeasureFacts Soundness.LowerRegions Soundness.WhileUpper
  Soundness.FiniteMatrix Soundness.LowerResidual.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** At most one indicator is nonzero. Thus local bounds on the individual
    weights give a global lower-potential bound, even with missing regions.
    Reuse the finite potential and integration lemmas introduced for upper bounds. *)
Lemma disjoint_region_potential_bound m regions weights (f : Valuation -> R) v :
  while_regions_disjoint m regions -> Rle R0 (f v) ->
  (forall j, Nat.lt j m -> satisfies v (regions j) -> Rle (weights j) (f v)) ->
  Rle (upper_region_potential m regions weights v) (f v).
Proof.
  induction m as [|m ih]; intros hd hf hw; first exact hf.
  have hd' : while_regions_disjoint m regions by intros i j hi hj; apply hd; lia.
  change (Rle (Rplus (upper_region_potential m regions weights v)
    (Rmult (weights m) (q_eval (QIndicator (regions m)) v))) (f v)).
  destruct (cformula_satisfies_dec (regions m) v) as [hm|hm].
  - have hz : upper_region_potential m regions weights v = R0.
    { apply finite_r_sum_zero => j hj.
      have he : ~ satisfies v (regions j).
      { intro hjv; have hdis := hd m j (Nat.lt_succ_diag_r m) hj v.
        cbn [c_not c_and satisfies] in hdis; tauto. }
      rewrite q_eval_indicatorE; rewrite (real_indicator_false _ he); exact: Rmult_0_r. }
    rewrite q_eval_indicatorE; rewrite hz (real_indicator_true _ hm) Rmult_1_r Rplus_0_l; apply hw; [lia|exact hm].
  - rewrite q_eval_indicatorE; rewrite (real_indicator_false _ hm) Rmult_0_r Rplus_0_r.
    apply ih; [exact hd'|exact hf|intros; apply hw; [lia|assumption] ].
Qed.

Lemma guarded_region_potential_zero m g regions weights v :
  while_regions_in_guard m g regions -> ~ satisfies v g ->
  upper_region_potential m regions weights v = R0.
Proof.
  move=> hg hv; apply finite_r_sum_zero => j hj.
  have he : ~ satisfies v (regions j) by intro h; apply hv; exact (hg j hj v h).
  rewrite q_eval_indicatorE; rewrite (real_indicator_false _ he); exact: Rmult_0_r.
Qed.

(** S_n is the finite matrix reward. Inside a region it is paid no faster
    than the corresponding finite semantic reward. Progress is not needed
    for this finite-horizon induction. *)
Theorem finite_loop_value_lower m g body q regions transitions exits :
  while_regions_disjoint m regions -> while_regions_in_guard m g regions ->
  (forall i, Nat.lt i m -> hoare_valid
    (p_concentrated_mass (regions i) (PConst R1)) body
    (while_body_post_lower m regions (transitions i) g q (exits i))) ->
  forall n i v, Nat.lt i m -> satisfies v (regions i) ->
  Rle (matrix_rewards m (lower_transition m regions transitions)
    (lower_exit m regions exits) n i) (finite_loop_value g (denote body) q n v).
Proof.
  move=> hd hg hb; induction n as [|n ih]; intros i v hi hv.
  - change (Rle R0 (finite_loop_value g (denote body) q 0 v)).
    apply/RleP; exact (proj1 (andP (finite_loop_value_bounds _ _ _ _ v))).
  - have hguard := hg i hi v hv.
    rewrite finite_loop_value_enterS //.
    set values := matrix_rewards m (lower_transition m regions transitions) (lower_exit m regions exits) n.
    set potential := upper_region_potential m regions values.
    set reward := q_eval (condition_pconstruct q (c_not g)).
    have hdom w : Rle (Rplus (reward w) (potential w)) (finite_loop_value g (denote body) q n w).
    { destruct (cformula_satisfies_dec g w) as [hw|hw].
      - have hr : reward w = R0.
        { rewrite /reward condition_pconstruct_correct.
          have hn : ~ satisfies w (c_not g) by cbn [c_not satisfies]; tauto.
          rewrite (real_indicator_false _ hn); exact: Rmult_0_l. }
        rewrite hr Rplus_0_l; apply disjoint_region_potential_bound.
        + exact hd.
        + apply/RleP; exact (proj1 (andP (finite_loop_value_bounds _ _ _ _ w))).
        + intros j hj hwj; exact (ih j w hj hwj).
      - rewrite /potential (guarded_region_potential_zero m g regions values w hg hw) Rplus_0_r.
        rewrite finite_loop_value_nonentry // /reward condition_pconstruct_correct
          (real_indicator_true _ hw) Rmult_1_l; apply Rle_refl. }
    have hm : Subprob (denote body v) by exact: sprob_kernel_le1.
    have hI : ConcreteMeasure.Integrable (denote body v) (finite_loop_value g (denote body) q n).
    { apply (@ConcreteMeasure.bounded_integrable _ Valuation (denote body v)
        (finite_loop_value g (denote body) q n) hm (finite_loop_value_measurable _ _ _ _)).
      - intro w; exact (proj1 (andP (finite_loop_value_bounds _ _ _ _ w))).
      - intro w; exact (proj2 (andP (finite_loop_value_bounds _ _ _ _ w))). }
    have hR : ConcreteMeasure.Integrable (denote body v) reward by exact: q_expectation_integrable.
    have hP := upper_region_potential_integrable m regions values _ hm.
    have hE := expectation_le_integrable _ _ _ (ConcreteMeasure.integrable_add hR hP) hI hdom.
    have hsplit := ConcreteMeasure.expectation_add hR hP.
    change (expectation (denote body v) (fun w => Rplus (reward w) (potential w)) =
      Rplus (expectation (denote body v) reward) (expectation (denote body v) potential)) in hsplit.
    rewrite hsplit /potential (upper_region_potential_expectation m regions values _ hm) in hE.
    have [ht hr] := lower_point_bounds m g body q regions transitions exits hb i v hi hv.
    have hs : Rle (matrix_apply m (lower_transition m regions transitions) values i)
      (finite_r_sum m (fun j => Rmult (values j)
        (expectation (denote body v) (q_eval (QIndicator (regions j)))))).
    { apply finite_r_sum_le => j hj; rewrite Rmult_comm; apply Rmult_le_compat_l.
      - exact (proj1 (lower_certificate_rewards_bounds m g body q regions transitions exits hb hd hg n j hj)).
      - exact (ht j hj). }
    change (Rle (Rplus (lower_exit m regions exits i)
      (matrix_apply m (lower_transition m regions transitions) values i))
      (expectation (denote body v) (finite_loop_value g (denote body) q n))).
    change (Rle (lower_exit m regions exits i) (expectation (denote body v) reward)) in hr; lra.
Qed.

(** Point inputs identify the forward reward approximation with its kernel
    value. This uses the existing transformer laws, not a second semantics. *)
Lemma loop_reward_approx_point g (k : Kernel) q n (v : Valuation) :
  loop_reward_approx g k q n (ConcreteMeasure.point v) = finite_loop_value g k q n v.
Proof.
  transitivity (expectation (transform (loop_approx g k n) (ConcreteMeasure.point v)) (q_eval q)).
  - apply expectation_measure_equiv => A mA; symmetry; apply transform_loop_approx.
    + exact: ConcreteMeasure.point_subprob.
    + exact mA.
  - apply expectation_measure_equiv => A mA; exact: transform_point.
Qed.

(** The pointwise finite reward converges to the same conditioned exit
    expectation that occurs in the declared Hoare rule. *)
Lemma finite_loop_value_exit_cvg g body q (v : Valuation) :
  (fun n => finite_loop_value g (denote body) q n v) @ \oo -->
  expectation (denote (CWhile g body) v) (q_eval (condition_pconstruct q (c_not g))).
Proof.
  set ps := {| pstate_measure := ConcreteMeasure.point v;
    pstate_prob_logic_values := fun _ => R0 |}.
  have hp : pstate_admissible ps by exact: ConcreteMeasure.point_subprob.
  have hc := run_while_reward_cvg g body q ps hp.
  have he : expectation (pstate_measure (run (CWhile g body) ps))
      (q_eval (condition_pconstruct q (c_not g))) =
    expectation (denote (CWhile g body) v) (q_eval (condition_pconstruct q (c_not g))).
  { apply expectation_measure_equiv => A mA; exact: transform_point. }
  rewrite he in hc.
  have hf : (fun n => loop_reward_approx g (denote body) q n (pstate_measure ps)) =
    (fun n => finite_loop_value g (denote body) q n v).
  { apply/funext => n; exact: loop_reward_approx_point. }
  by rewrite hf in hc.
Qed.
