(** Proved compatibility facts for the historical calculation clients.
    This file imports no example-specific analytical assumption. *)
From Stdlib Require Import Reals Lra Field FunctionalExtensionality.
From mathcomp Require Import boot order ssralg ssrnum interval interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences exp numfun measure.
From mathcomp Require Import trigonometry_functions.
From mathcomp Require Import measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import lebesgue_stieltjes_measure Rstruct Rstruct_topology.
Require Export Soundness.RealIntegrationFacts Soundness.DistributionFacts
  Soundness.ConstructFacts Soundness.StateSpace.
Require Import AnalysisPrelude MeasureIntegration DistributionKernels CPHL.
Require Import Soundness.DensityIntegration.

Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports MeasurableR ValuationSpace.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Reuse the existing real-number bridges for these elementary bounds.
    Their Stdlib analysis proofs pull in a separate [classic] dependency;
    MathComp proves the same facts from the foundations already in use. *)
Lemma real_exp_strict_mono (x y : R) :
  Rlt x y -> Rlt (Rtrigo_def.exp x) (Rtrigo_def.exp y).
Proof.
  move=> /RltP h; apply/RltP.
  by rewrite !StandardReal.exp ltr_expR.
Qed.

Lemma real_pi_lt_four : Rlt PI (IZR 4).
Proof.
  have hp := @trigonometry_functions.pihalf_lt2 real.
  have hr : Rlt (Rdiv PI (IZR 2)) (IZR 2).
  { apply/RltP; rewrite StandardReal.pi; exact hp. }
  lra.
Qed.

Definition real_measurable (f : R -> R) : Prop :=
  @measurable_fun _ _ RealIntegration.Space RealIntegration.Space setT f.
Definition real_event_measurable (A : R -> Prop) : Prop :=
  @measurable _ RealIntegration.Space A.

(** Extensionality transfers regularity along the same pointwise equalities
    that the examples use to simplify their integrands. *)
Lemma real_integrable_ext (f g : R -> R) :
  (forall x, f x = g x) -> real_integrable f -> real_integrable g.
Proof. move=> /functional_extensionality ->; exact. Qed.

Lemma real_integrable_scale c f : real_integrable f ->
  real_integrable (fun x => Rmult c (f x)).
Proof. exact: ConcreteMeasure.integrable_scale. Qed.

Lemma real_measurable_below a : real_event_measurable (fun x => Rlt x a).
Proof.
have -> : (fun x => Rlt x a) = `]-oo, a[%classic.
  by rewrite predeqE => x; rewrite /= in_itv/=; split=> /RltP.
exact: measurable_itv.
Qed.
Lemma real_measurable_above a : real_event_measurable (fun x => Rle a x).
Proof.
have -> : (fun x => Rle a x) = `[a, +oo[%classic.
  by rewrite predeqE => x; rewrite /= in_itv/= andbT; split=> /RleP.
exact: measurable_itv.
Qed.
Lemma real_measurable_between a b :
  real_event_measurable (fun x => Rle a x /\ Rlt x b).
Proof. apply: measurableI; [exact: real_measurable_above|exact: real_measurable_below]. Qed.

(** Multiplication by a measurable indicator cannot destroy integrability. *)
Lemma real_integrable_mask A f : real_event_measurable A -> real_integrable f ->
  real_integrable (fun x => Rmult (real_indicator (A x)) (f x)).
Proof.
move=> mA hf.
rewrite /real_integrable /ConcreteMeasure.Integrable.
apply: (@eq_integrable _ RealIntegration.Space real RealIntegration.lebesgue
  setT measurableT (fun x => (\1_A x)%:E * (f x)%:E)).
- by move=> x _; rewrite /= IndicatorExpectation.indicatorE EFinM.
- apply: integrableMr => //.
  exists 1%R; split=> // r r1 x _ /=; rewrite indicE.
  apply: (le_trans _ (ltW r1)).
  by rewrite normr_nat lern1 leq_b1.
Qed.

(** A continuous function is integrable on a bounded interval. Restriction
    from the compact closed interval justifies the half-open public notation. *)
Lemma real_integrable_between_continuous (a b : real) (f : real -> real) :
  continuous f ->
  real_integrable (fun x => Rmult (real_indicator (Rle a x /\ Rlt x b)) (f x)).
Proof.
move=> cf.
have hi : integrable RealIntegration.lebesgue `[a,b[ (EFin \o f).
  apply: (integrableS (E := `[a,b])) => //; try exact: measurable_itv.
  - by move=> x; rewrite /= !in_itv/= => /andP[ha /ltW hb]; apply/andP.
  - apply: continuous_compact_integrable; first exact: segment_compact.
    exact: continuous_subspaceT.
apply: (eq_integrable measurableT ((EFin \o f) \_ `[a,b[)).
- move=> x _; rewrite patchE; case: ifP => h /=.
  + have /andP [/RleP ha /RltP hb] : (a <= x < b)%R.
      by move/set_mem: h; rewrite /= in_itv/=.
    by rewrite real_indicator_true// Rmult_1_l.
  + rewrite real_indicator_false ?Rmult_0_l//.
    move=> [/RleP ha /RltP hb].
    have hx : x \in `[a,b[%classic.
      by apply/mem_set; rewrite /= in_itv/= ha hb.
    by move: h; rewrite hx.
- exact/(integrable_mkcond _ (measurable_itv _)).1.
Qed.

Lemma real_integrable_between_one a b :
  real_integrable (fun x => Rmult (real_indicator (Rle a x /\ Rlt x b)) R1).
Proof. apply: real_integrable_between_continuous; exact: cst_continuous. Qed.

Lemma real_integrable_exp_between a b k :
  real_integrable (fun x => Rmult (real_indicator (Rle a x /\ Rlt x b))
    (Rtrigo_def.exp (Rmult k x))).
Proof.
apply: real_integrable_between_continuous => x.
under eq_fun do rewrite RexpE.
apply: continuous_comp; last exact: continuous_expR.
by apply: continuousM => //; exact: cst_continuous.
Qed.

Lemma real_integrable_laplace location scale : Rlt 0 scale ->
  real_integrable (fun z => Rmult (Rdiv 1 (Rmult 2 scale))
    (Rtrigo_def.exp (Rdiv (Ropp (Rabs (Rminus z location))) scale))).
Proof.
move=> hs; exact: (@distribution_density_integrable
  (Laplace (TConst location) (TConst scale)) demo_valuation hs).
Qed.

(** Sampling measures and raw densities agree for measurable nonnegative
    rewards under valid parameters. Both sides use the total real projection;
    construct rewards are integrable by [q_integral_integrable]. Invalid laws
    are deliberately excluded from this density identity. *)
Lemma distribution_expectation_density d v (f : real -> real) :
  distribution_valid d v -> real_measurable f ->
  (forall x, (0 <= f x)%R) ->
  ConcreteMeasure.expectation (distribution_measure d v) f =
    real_integral (fun x => Rmult (distribution_density d v x) (f x)).
Proof.
move=> hd mf f0; rewrite /real_integral /ConcreteMeasure.expectation /Rintegral.
congr (fine _); symmetry.
transitivity (\int[RealIntegration.lebesgue]_x ((f x)%:E * (distribution_density d v x)%:E)).
- by apply: eq_integral => x _; rewrite EFinM muleC.
- apply: integral_density_from_events.
  + exact: distribution_density_measurable.
  + move=> x; exact: distribution_density_nonnegative.
  + move=> A _; exact: distribution_density_event.
  + by move=> x; rewrite lee_fin.
  + exact/measurable_EFinP.
Qed.

Lemma q_integral_density x d q v : distribution_valid d v ->
  q_eval (QIntegral x d q) v =
    real_integral (fun z => Rmult (distribution_density d v z)
      (q_eval q (update_real v x z))).
Proof.
move=> hd; apply: distribution_expectation_density => //.
- exact: measurable_fun_pair2 (measurable_construct_update x (q_eval_measurable q)).
- move=> z; exact: q_eval_nonnegative.
Qed.

(** Function equalities rewrite beneath nested integral binders without
    unfolding the implementation of a measure. The universal validity premise
    is discharged for the examples' constant positive scales and intervals. *)
Lemma q_eval_integral_density x d q : (forall v, distribution_valid d v) ->
  q_eval (QIntegral x d q) = fun v =>
    real_integral (fun z => Rmult (distribution_density d v z)
      (q_eval q (update_real v x z))).
Proof. move=> hd; apply: functional_extensionality => v; exact: q_integral_density. Qed.

Local Open Scope R_scope.

(** Integrable exponential tails are restrictions of a scaled, normalized
    Laplace density. No closed-form exponential integral is assumed here. *)
Lemma real_integrable_exp_below a k : 0 < k ->
  real_integrable (fun x => real_indicator (x < a) * exp (k * x)).
Proof.
  intro Hk.
  eapply real_integrable_ext with
    (f := fun x => real_indicator (x < a) *
      (((2 / k) * exp (k * a)) *
        ((1 / (2 * (1 / k))) * exp (- Rabs (x - a) / (1 / k))))).
  - intro x; destruct (Rlt_dec x a) as [Hx|Hx].
    + rewrite (real_indicator_true _ Hx) !Rmult_1_l.
      replace (((2 / k) * exp (k * a)) *
        ((1 / (2 * (1 / k))) * exp (- Rabs (x - a) / (1 / k))))
        with (exp (k * a) * exp (- Rabs (x - a) / (1 / k))) by (field; lra).
      rewrite -exp_plus (Rabs_left (x - a) (ltac:(lra))).
      f_equal; field; lra.
    + rewrite (real_indicator_false _ Hx); ring.
  - apply real_integrable_mask; [apply real_measurable_below|].
    apply real_integrable_scale, real_integrable_laplace.
    apply Rdiv_lt_0_compat; lra.
Qed.

Lemma real_integrable_exp_above a k : k < 0 ->
  real_integrable (fun x => real_indicator (a <= x) * exp (k * x)).
Proof.
  intro Hk.
  eapply real_integrable_ext with
    (f := fun x => real_indicator (a <= x) *
      (((-2 / k) * exp (k * a)) *
        ((1 / (2 * (-1 / k))) * exp (- Rabs (x - a) / (-1 / k))))).
  - intro x; destruct (Rle_dec a x) as [Hx|Hx].
    + rewrite (real_indicator_true _ Hx) !Rmult_1_l.
      replace (((-2 / k) * exp (k * a)) *
        ((1 / (2 * (-1 / k))) * exp (- Rabs (x - a) / (-1 / k))))
        with (exp (k * a) * exp (- Rabs (x - a) / (-1 / k))) by (field; lra).
      rewrite -exp_plus (Rabs_right (x - a) (ltac:(lra))).
      f_equal; field; lra.
    + rewrite (real_indicator_false _ Hx); ring.
  - apply real_integrable_mask; [apply real_measurable_above|].
    apply real_integrable_scale, real_integrable_laplace.
    replace (-1 / k) with (1 / -k) by (field; lra).
    apply Rdiv_lt_0_compat; lra.
Qed.

(** Regularity follows the algebraic rearrangements used by regional
    calculations. Equality is needed only inside the masked event. *)
Lemma real_integrable_mask_right A f :
  real_event_measurable A -> real_integrable f ->
  real_integrable (fun x => f x * real_indicator (A x)).
Proof.
  intros HA Hf; eapply real_integrable_ext.
  - intro x; apply Rmult_comm.
  - apply real_integrable_mask; assumption.
Qed.
Lemma real_integrable_mask_scale A c f :
  real_integrable (fun x => real_indicator (A x) * f x) ->
  real_integrable (fun x => real_indicator (A x) * (c * f x)).
Proof.
  intro Hf; eapply real_integrable_ext with
    (f := fun x => c * (real_indicator (A x) * f x)).
  - intro x; ring.
  - exact (real_integrable_scale c _ Hf).
Qed.
Lemma real_integrable_mask_add A f g :
  real_integrable (fun x => real_indicator (A x) * f x) ->
  real_integrable (fun x => real_indicator (A x) * g x) ->
  real_integrable (fun x => real_indicator (A x) * (f x + g x)).
Proof.
  intros Hf Hg; eapply real_integrable_ext with
    (f := fun x => real_indicator (A x) * f x + real_indicator (A x) * g x).
  - intro x; ring.
  - exact (@ConcreteMeasure.integrable_add _ RealIntegration.Space
      RealIntegration.lebesgue _ _ Hf Hg).
Qed.
Lemma real_integrable_mask_ext A f g :
  (forall x, A x -> f x = g x) ->
  real_integrable (fun x => real_indicator (A x) * g x) ->
  real_integrable (fun x => real_indicator (A x) * f x).
Proof.
  intros Heq Hg; eapply real_integrable_ext; [|exact Hg].
  (** General events use the same classical decision as their indicators. *)
  intro x; destruct (boolp.pselect (A x)) as [Hx|Hx].
  - rewrite (Heq x Hx); reflexivity.
  - rewrite (real_indicator_false _ Hx); ring.
Qed.
Lemma real_integrable_between_constant a b c :
  real_integrable (fun x => real_indicator (a <= x /\ x < b) * c).
Proof.
  eapply real_integrable_ext with
    (f := fun x => real_indicator (a <= x /\ x < b) * (c * 1)).
  - intro x; ring.
  - apply real_integrable_mask_scale, real_integrable_between_one.
Qed.

(** Kernel linearity suffices for partitions of probability constructs;
    unlike raw-density rewriting, this also covers zero invalid kernels. *)
Lemma q_integral_partition x d p q r :
  (forall v, q_eval p v + q_eval q v = q_eval r v) ->
  forall v, q_eval (QIntegral x d p) v + q_eval (QIntegral x d q) v =
    q_eval (QIntegral x d r) v.
Proof.
  intros Hpartition v.
  change (ConcreteMeasure.expectation (distribution_measure d v)
    (fun z => q_eval p (update_real v x z)) +
    ConcreteMeasure.expectation (distribution_measure d v)
    (fun z => q_eval q (update_real v x z)) =
    ConcreteMeasure.expectation (distribution_measure d v)
    (fun z => q_eval r (update_real v x z))).
  transitivity (ConcreteMeasure.expectation (distribution_measure d v)
    (fun z => q_eval p (update_real v x z) + q_eval q (update_real v x z))).
  - symmetry; exact (@ConcreteMeasure.expectation_add _ RealIntegration.Space
      (distribution_measure d v) _ _ (q_integral_integrable x d p v)
        (q_integral_integrable x d q v)).
  - apply ConcreteMeasure.expectation_ext; intro z; apply Hpartition.
Qed.

(** A real total mass of one cannot be the projection of an infinite mass,
    since that projection is zero. This recovers admissibility from an
    existing normalized-state assertion without strengthening its contract. *)
Lemma subprob_of_mass_one (mu : Measure) :
  measure_of mu (fun _ => True) = R1 -> Subprob mu.
Proof.
  rewrite /measure_of /ConcreteMeasure.event_mass /Subprob /ConcreteMeasure.Subprob.
  case: (mu setT) => [r | |] /=.
  - move=> ->; exact: lexx.
  - intro H; exfalso; change (Rdefinitions.R0 = Rdefinitions.R1) in H; lra.
  - intro H; exfalso; change (Rdefinitions.R0 = Rdefinitions.R1) in H; lra.
Qed.

(** Explicit closure facts for the finite Boolean event partitions used by
    the examples. Arbitrary assertions are not presumed measurable. *)
Lemma measurable_assertion_true : measurable_assertion (fun _ => True).
Proof. exact: measurableT. Qed.
Lemma measurable_assertion_not A : measurable_assertion A ->
  measurable_assertion (fun v => ~ A v).
Proof. exact: measurableC. Qed.
Lemma measurable_assertion_and A B : measurable_assertion A ->
  measurable_assertion B -> measurable_assertion (fun v => A v /\ B v).
Proof. exact: measurableI. Qed.
