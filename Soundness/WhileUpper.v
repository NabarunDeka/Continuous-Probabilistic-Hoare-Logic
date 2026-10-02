(** Upper while certificates bound finite exit rewards. Coverage is enough:
    regions may overlap or extend outside the guard, and bodies may lose mass. *)
From Stdlib Require Import Reals Lra Lia.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences measure numfun measurable_realfun.
From mathcomp Require Import lebesgue_integral lebesgue_stieltjes_measure kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration CPHL Soundness.ConstructFacts Soundness.CommandFacts
  Soundness.LoopFacts Soundness.TransformerFacts Soundness.AssertionLogic
  Soundness.Conditioning Soundness.ConditioningAssertions Soundness.InputDecomposition
  Soundness.LoopRewards Soundness.FiniteExpectationBounds.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Pointwise finite rewards have a measurable [0,1]-valued interpretation,
    so they can also be integrated against arbitrary admissible inputs. *)
Definition finite_loop_value g k q n (v : Valuation) : R :=
  expectation (loop_approx g k n v) (q_eval q).

Lemma finite_loop_value_measurable g k q n :
  @measurable_fun _ _ [the measurableType _ of Valuation]
    [the measurableType _ of (real : Type)] setT (finite_loop_value g k q n).
Proof. exact (@kernel_expectation_measurable (loop_approx g k n) (q_eval q) (q_eval_measurable q) (q_eval_nonnegative q)). Qed.

Lemma finite_loop_value_bounds g k q n v :
  (0 <= finite_loop_value g k q n v <= 1)%R.
Proof. apply: q_expectation_bounds; exact: sprob_kernel_le1. Qed.

Lemma finite_loop_value_enter0 g k q (v : Valuation) : satisfies v g ->
  finite_loop_value g k q 0 v = 0%R.
Proof.
  move=> hv; have hg : cformula_eval_bool g v = true by apply/cformula_eval_bool_spec.
  transitivity (expectation (ConcreteMeasure.zero : Measure) (q_eval q)); last exact: q_expectation_zero.
  apply expectation_measure_equiv => A mA.
  change (loop_exit g k 0 v A = 0); by rewrite loop_exit0 hg.
Qed.

Lemma finite_loop_value_nonentry g k q n (v : Valuation) : ~ satisfies v g ->
  finite_loop_value g k q n v = q_eval q v.
Proof.
  move=> hv; have hg : cformula_eval_bool g v = false.
  { apply/negbTE; apply/negP => /cformula_eval_bool_spec; exact hv. }
  transitivity (expectation (ConcreteMeasure.point v) (q_eval q)); last exact: q_expectation_point.
  apply expectation_measure_equiv => A mA.
  case: n => [|n]; [change (loop_exit g k 0 v A = dirac v A); rewrite loop_exit0 hg|
    rewrite loop_approxS hg]; reflexivity.
Qed.

Lemma finite_loop_value_enterS g k q n (v : Valuation) : satisfies v g ->
  finite_loop_value g k q n.+1 v = expectation (k v) (finite_loop_value g k q n).
Proof.
  move=> hv; have hg : cformula_eval_bool g v = true by apply/cformula_eval_bool_spec.
  transitivity (expectation (transform (loop_approx g k n) (k v)) (q_eval q)).
  - apply expectation_measure_equiv => A mA; by rewrite loop_approxS hg transform_event.
  - apply transform_expectation; try exact: q_eval_measurable;
      try exact: q_eval_nonnegative; try exact: q_eval_le_one; exact: sprob_kernel_le1.
Qed.

Lemma loop_reward_approx_integral g k q n mu : Subprob mu ->
  loop_reward_approx g k q n mu = expectation mu (finite_loop_value g k q n).
Proof.
  move=> hm; transitivity (expectation (transform (loop_approx g k n) mu) (q_eval q)).
  - apply expectation_measure_equiv => A mA; symmetry; exact: transform_loop_approx.
  - apply transform_expectation; try exact: q_eval_measurable;
      try exact: q_eval_nonnegative; try exact: q_eval_le_one; exact hm.
Qed.

(** A unit point in a region is an admissible body input, even when that
    region extends outside the guard. Empty regions need no such witness. *)
Lemma while_upper_body_point m g body q regions transitions exits :
  (forall i, Nat.lt i m -> hoare_valid
    (p_concentrated_mass (regions i) (PConst 1%R)) body
    (while_body_post_upper m regions (transitions i) g q (exits i))) ->
  forall i (v : Valuation), Nat.lt i m -> satisfies v (regions i) ->
  (forall j, Nat.lt j m -> Rle
    (expectation (denote body v) (q_eval (QIndicator (regions j)))) (transitions i j)) /\
  Rle (expectation (denote body v) (q_eval (condition_pconstruct q (c_not g)))) (exits i).
Proof.
  move=> hb i v hi hv.
  set ps := {| pstate_measure := ConcreteMeasure.point v;
    pstate_prob_logic_values := fun _ => 0%R |}.
  have hp : psatisfies ps (p_concentrated_mass (regions i) (PConst 1%R)).
  { rewrite /p_concentrated_mass psatisfies_and !psatisfies_eq.
    cbn [pterm_eval ps pstate_measure].
    rewrite !q_expectation_point.
    have ht : q_eval (QIndicator c_true) v = 1%R by apply formula_indicator_true; cbn [c_true satisfies]; tauto.
    have hc : q_eval (QIndicator (regions i)) v = 1%R by apply formula_indicator_true.
    by rewrite ht hc. }
  have hout := hb i hi ps (ConcreteMeasure.point_subprob v) hp.
  rewrite /while_body_post_upper psatisfies_and psatisfies_finite_p_and in hout.
  have he q' : expectation (pstate_measure (run body ps)) (q_eval q') =
    expectation (denote body v) (q_eval q').
  { apply expectation_measure_equiv => A mA; exact: transform_point. }
  destruct hout as [ht he']; split.
  - move=> j hj; have h := ht j hj; change (Rle (expectation (pstate_measure (run body ps))
      (q_eval (QIndicator (regions j)))) (transitions i j)) in h; by rewrite he in h.
  - change (Rle (expectation (pstate_measure (run body ps))
      (q_eval (condition_pconstruct q (c_not g)))) (exits i)) in he'; by rewrite he in he'.
Qed.

(** This potential overcounts overlaps and can exceed one. Its integrability
    follows from a finite sum of bounded indicators, not a probability bound. *)
Definition upper_region_potential m regions (solution : nat -> R) v : R :=
  finite_r_sum m (fun j => Rmult (solution j) (q_eval (QIndicator (regions j)) v)).

Lemma upper_region_potential_integrable m regions solution mu : Subprob mu ->
  ConcreteMeasure.Integrable mu (upper_region_potential m regions solution).
Proof.
  move=> hm; apply integrable_finite_r_sum => i hi.
  apply ConcreteMeasure.integrable_scale; exact: q_expectation_integrable.
Qed.

Lemma upper_region_potential_expectation m regions solution mu : Subprob mu ->
  expectation mu (upper_region_potential m regions solution) =
  finite_r_sum m (fun j => Rmult (solution j)
    (expectation mu (q_eval (QIndicator (regions j))))).
Proof.
  move=> hm.
  have hI i : ConcreteMeasure.Integrable mu
    (fun v => Rmult (solution i) (q_eval (QIndicator (regions i)) v)).
  { apply ConcreteMeasure.integrable_scale; exact: q_expectation_integrable. }
  rewrite /upper_region_potential (expectation_finite_r_sum mu m _ (fun i _ => hI i)).
  congr (finite_r_sum m _); apply/funext => i.
  apply ConcreteMeasure.expectation_scale; exact: q_expectation_integrable.
Qed.

(** Finite-horizon induction: exit reward is paid immediately outside the
    guard; inside, coverage supplies at least one region's continuation bound. *)
Theorem finite_loop_value_upper m g body q regions solution transitions exits :
  while_regions_cover m g regions ->
  (forall i, Nat.lt i m -> hoare_valid
    (p_concentrated_mass (regions i) (PConst 1%R)) body
    (while_body_post_upper m regions (transitions i) g q (exits i))) ->
  while_upper_solution m solution transitions exits ->
  forall n i v, Nat.lt i m -> satisfies v g -> satisfies v (regions i) ->
    Rle (finite_loop_value g (denote body) q n v) (solution i).
Proof.
  move=> hcover hbody hsol; induction n as [|n ih]; intros i v hi hg hreg.
  - rewrite finite_loop_value_enter0 //; exact (proj1 (proj2 (hsol i hi))).
  - rewrite finite_loop_value_enterS //.
    have hm : Subprob (denote body v) by exact: sprob_kernel_le1.
    have hpoint := while_upper_body_point m g body q regions transitions exits hbody i v hi hreg.
    set reward := q_eval (condition_pconstruct q (c_not g)).
    set potential := upper_region_potential m regions solution.
    have hdom w : Rle (finite_loop_value g (denote body) q n w)
      (Rplus (reward w) (potential w)).
    { have hp0 : Rle 0 (potential w).
      { apply finite_r_sum_nonnegative => j hj; apply Rmult_le_pos.
        - exact (proj1 (proj2 (hsol j hj))).
        - apply/RleP; exact: q_eval_nonnegative. }
      have hr0 : Rle 0 (reward w) by apply/RleP; exact: q_eval_nonnegative.
      destruct (cformula_satisfies_dec g w) as [hw|hw].
      - have [j [hj hr] ] := proj1 (satisfies_finite_c_or m regions w) (hcover w hw).
        have hih := ih j w hj hw hr.
        have hmem := finite_r_sum_member_le m
          (fun j => Rmult (solution j) (q_eval (QIndicator (regions j)) w)) j hj.
        have hind : q_eval (QIndicator (regions j)) w = 1%R by apply formula_indicator_true.
        have hsum : Rle (solution j) (potential w).
        { have heq : Rmult (solution j) (q_eval (QIndicator (regions j)) w) = solution j.
          { rewrite hind; exact: Rmult_1_r. }
          rewrite -{1}heq; apply hmem => l hl.
          apply Rmult_le_pos; [exact (proj1 (proj2 (hsol l hl)))|apply/RleP; exact: q_eval_nonnegative]. }
        lra.
      - rewrite finite_loop_value_nonentry //.
        have hr : reward w = q_eval q w.
        { rewrite /reward condition_pconstruct_correct (real_indicator_true _ hw); exact: Rmult_1_l. }
        rewrite hr; lra. }
    have hint : ConcreteMeasure.Integrable (denote body v) (finite_loop_value g (denote body) q n).
    { apply (@ConcreteMeasure.bounded_integrable _ Valuation (denote body v)
        (finite_loop_value g (denote body) q n) hm (finite_loop_value_measurable g (denote body) q n)).
      - move=> w; exact (proj1 (andP (finite_loop_value_bounds _ _ _ _ w))).
      - move=> w; exact (proj2 (andP (finite_loop_value_bounds _ _ _ _ w))). }
    have hir : ConcreteMeasure.Integrable (denote body v) reward by exact: q_expectation_integrable.
    have hip := upper_region_potential_integrable m regions solution _ hm.
    have hb := expectation_le_integrable _ _ _ hint (ConcreteMeasure.integrable_add hir hip) hdom.
    have hsplit := ConcreteMeasure.expectation_add hir hip.
    change (expectation (denote body v) (fun w => Rplus (reward w) (potential w)) =
      Rplus (expectation (denote body v) reward) (expectation (denote body v) potential)) in hsplit.
    rewrite hsplit /potential (upper_region_potential_expectation m regions solution _ hm) in hb.
    have hsum : Rle (finite_r_sum m (fun j => Rmult (solution j)
      (expectation (denote body v) (q_eval (QIndicator (regions j))))))
      (finite_r_sum m (fun j => Rmult (transitions i j) (solution j))).
    { apply finite_r_sum_le => j hj; rewrite Rmult_comm; apply Rmult_le_compat_r.
      - exact (proj1 (proj2 (hsol j hj))).
      - exact (proj1 hpoint j hj). }
    have hr := proj2 hpoint; have hs := proj1 (hsol i hi).
    change (Rle (expectation (denote body v) reward) (exits i)) in hr.
    lra.
Qed.

(** Concentration is only almost sure. Replace the input by its restriction
    before integrating the pointwise estimate; no input mass is divided out. *)
Theorem loop_reward_approx_upper m k g body q regions solution transitions exits ps :
  Nat.lt k m -> while_regions_cover m g regions ->
  (forall i, Nat.lt i m -> hoare_valid
    (p_concentrated_mass (regions i) (PConst 1%R)) body
    (while_body_post_upper m regions (transitions i) g q (exits i))) ->
  while_upper_solution m solution transitions exits ->
  pstate_admissible ps -> psatisfies ps (p_almost_sure (c_and g (regions k))) ->
  forall n, Rle (loop_reward_approx g (denote body) q n (pstate_measure ps))
    (Rmult (solution k) (measure_of (pstate_measure ps) (fun _ => True))).
Proof.
  move=> hk hc hb hs hp hpre n.
  have [he _] := almost_sure_restriction_equiv (c_and g (regions k)) ps hp hpre.
  rewrite loop_reward_approx_integral //.
  rewrite -(expectation_measure_equiv _ _ _ he).
  have hm := expectation_restrict_bound (pstate_measure ps) (c_and g (regions k))
    (finite_loop_value g (denote body) q n) (solution k) hp
    (finite_loop_value_measurable _ _ _ _).
  have hbound : Rle (expectation (pstate_measure (condition_state (c_and g (regions k)) ps))
    (finite_loop_value g (denote body) q n))
    (Rmult (solution k) (measure_of (pstate_measure ps) (formula_event (c_and g (regions k))))).
  { apply/RleP; apply hm.
    - move=> w; exact (proj1 (andP (finite_loop_value_bounds _ _ _ _ w))).
    - move=> w; exact (proj2 (andP (finite_loop_value_bounds _ _ _ _ w))).
    - apply/RleP; exact (proj1 (proj2 (hs k hk))).
    - move=> w hw; have [hg hr] : satisfies w g /\ satisfies w (regions k).
      { (** Decode conjunction through the same classical library as assertions. *)
        change (~ (satisfies w g -> ~ satisfies w (regions k))) in hw.
        rewrite boolp.not_implyE boolp.not_notE in hw; exact hw. }
      apply/RleP; exact (finite_loop_value_upper m g body q regions solution transitions exits hc hb hs n k w hk hg hr). }
  have hmass : measure_of (pstate_measure ps) (formula_event (c_and g (regions k))) =
    measure_of (pstate_measure ps) (fun _ => True).
  { rewrite -restriction_formula_mass /measure_of /ConcreteMeasure.event_mass (he setT measurableT); reflexivity. }
  by rewrite hmass in hbound.
Qed.

(** Only bounded reward expectations pass through the limit. The theorem's
    recursive premise is semantic validity, ready for derivation induction. *)
Theorem hoare_valid_while_upper m k g body q regions solution transitions exits y :
  Nat.lt k m -> while_regions_cover m g regions ->
  (forall i, Nat.lt i m -> hoare_valid
    (p_concentrated_mass (regions i) (PConst 1%R)) body
    (while_body_post_upper m regions (transitions i) g q (exits i))) ->
  while_upper_solution m solution transitions exits ->
  hoare_valid (p_concentrated_mass_upper (c_and g (regions k)) (PVar y))
    (CWhile g body)
    (PFLe (PExpect (condition_pconstruct q (c_not g)))
      (PMul (PConst (solution k)) (PVar y))).
Proof.
  move=> hk hc hb hs ps hp /psatisfies_and [hreg hmass].
  have hfinite := loop_reward_approx_upper m k g body q regions solution transitions exits ps hk hc hb hs hp hreg.
  have hlimit := run_while_reward_cvg g body q ps hp.
  have hbound : (expectation (pstate_measure (run (CWhile g body) ps))
      (q_eval (condition_pconstruct q (c_not g))) <=
    solution k * measure_of (pstate_measure ps) (fun _ => True))%R.
  { apply: (cvgr_to_le hlimit); apply: nearW => n; exact/RleP/hfinite. }
  change (Rle (expectation (pstate_measure ps) (q_eval (QIndicator c_true)))
    (pstate_prob_logic_values ps y)) in hmass.
  rewrite expectation_indicator -[formula_assertion c_true]/(formula_event c_true) formula_event_true in hmass.
  change (Rle (expectation (pstate_measure (run (CWhile g body) ps))
    (q_eval (condition_pconstruct q (c_not g))))
    (Rmult (solution k) (pstate_prob_logic_values ps y))).
  eapply Rle_trans; [exact (elimT RleP hbound)|apply Rmult_le_compat_l; [exact (proj1 (proj2 (hs k hk)))|exact hmass] ].
Qed.
