(** Historical distribution/example calculations, separated from the concrete
    semantic foundation. Their analytical obligations are tracked separately;
    CPHL and Soundness must never import this file. *)
From Stdlib Require Import Reals Lra Field Ring.
Require Import CPHL.
Require Export Soundness.CalculationFacts.
Require Import Soundness.DistributionFacts.
(** The generic region operators now come from the concrete shared interface. *)
Open Scope R_scope.

(** Closure supplies the integrability premise for a finite partition. *)
Lemma real_integrable_add : forall f g : R -> R,
  real_integrable f -> real_integrable g ->
  real_integrable (fun x => f x + g x).
Proof.
  exact (@MeasureIntegration.ConcreteMeasure.integrable_add
    _ RealIntegration.Space RealIntegration.lebesgue).
Qed.

Lemma real_integral_scale_right :
  forall (c : R) (f : R -> R),
    real_integrable f ->
    real_integral (fun x => f x * c) = (real_integral f * c)%R.
Proof.
  intros c f Hf.
  transitivity (real_integral (fun x => c * f x)).
  - apply real_integral_extensional; intro x; ring.
  - rewrite real_integral_scale by assumption; ring.
Qed.

Lemma real_integral_below_add :
  forall (a : R) (f g : R -> R),
    real_integrable (fun x => real_indicator (x < a)%R * f x) ->
    real_integrable (fun x => real_indicator (x < a)%R * g x) ->
    real_integral_below a (fun x => f x + g x) =
      (real_integral_below a f + real_integral_below a g)%R.
Proof.
  intros a f g Hf Hg.
  unfold real_integral_below.
  transitivity
    (real_integral
      (fun x =>
        real_indicator (x < a)%R * f x +
        real_indicator (x < a)%R * g x)).
  - apply real_integral_extensional; intro x; ring.
  - apply real_integral_add; assumption.
Qed.

Lemma real_integral_between_add :
  forall (a b : R) (f g : R -> R),
    real_integrable (fun x => real_indicator (a <= x < b)%R * f x) ->
    real_integrable (fun x => real_indicator (a <= x < b)%R * g x) ->
    real_integral_between a b (fun x => f x + g x) =
      (real_integral_between a b f + real_integral_between a b g)%R.
Proof.
  intros a b f g Hf Hg.
  unfold real_integral_between.
  transitivity
    (real_integral
      (fun x =>
        real_indicator (a <= x < b)%R * f x +
        real_indicator (a <= x < b)%R * g x)).
  - apply real_integral_extensional; intro x; ring.
  - apply real_integral_add; assumption.
Qed.

Lemma real_integral_above_add :
  forall (a : R) (f g : R -> R),
    real_integrable (fun x => real_indicator (a <= x)%R * f x) ->
    real_integrable (fun x => real_indicator (a <= x)%R * g x) ->
    real_integral_above a (fun x => f x + g x) =
      (real_integral_above a f + real_integral_above a g)%R.
Proof.
  intros a f g Hf Hg.
  unfold real_integral_above.
  transitivity
    (real_integral
      (fun x =>
        real_indicator (a <= x)%R * f x +
        real_indicator (a <= x)%R * g x)).
  - apply real_integral_extensional; intro x; ring.
  - apply real_integral_add; assumption.
Qed.

Lemma real_integral_below_scale :
  forall (a c : R) (f : R -> R),
    real_integrable (fun x => real_indicator (x < a)%R * f x) ->
    real_integral_below a (fun x => c * f x) =
      (c * real_integral_below a f)%R.
Proof.
  intros a c f Hf.
  unfold real_integral_below.
  transitivity
    (real_integral (fun x => c * (real_indicator (x < a)%R * f x))).
  - apply real_integral_extensional; intro x; ring.
  - apply real_integral_scale; assumption.
Qed.

Lemma real_integral_between_scale :
  forall (a b c : R) (f : R -> R),
    real_integrable (fun x => real_indicator (a <= x < b)%R * f x) ->
    real_integral_between a b (fun x => c * f x) =
      (c * real_integral_between a b f)%R.
Proof.
  intros a b c f Hf.
  unfold real_integral_between.
  transitivity
    (real_integral
      (fun x => c * (real_indicator (a <= x < b)%R * f x))).
  - apply real_integral_extensional; intro x; ring.
  - apply real_integral_scale; assumption.
Qed.

(** Interval and singleton identities are now proved in RealIntegrationFacts. *)




Lemma real_integral_uniform_density :
  forall a b : R,
    (a < b)%R ->
    real_integral
      (fun x => real_indicator (a <= x /\ x <= b)%R / (b - a)) = 1%R.
Proof.
  intros a b Hab.
  (* Use the concrete normalization theorem; integrability is established
     with the distribution foundation, rather than assumed by scaling. *)
  exact (@real_integral_distribution_density
    (Uniform (TConst a) (TConst b)) demo_valuation Hab).
Qed.

(** Trusted geometric law for the unit-square quarter disk.  It follows the
    nested integration order used by two sequential uniform samples. *)
Axiom real_integral_unit_square_quarter_disk :
  real_integral
    (fun x =>
      real_indicator (0 <= x /\ x <= 1)%R *
      real_integral
        (fun y =>
          real_indicator (0 <= y /\ y <= 1)%R *
          real_indicator (x * x + y * y <= 1)%R)) = (PI / 4)%R.

Lemma real_integral_between_constant :
  forall a b c : R,
    (a <= b)%R ->
    real_integral_between a b (fun _ : R => c) = (c * (b - a))%R.
Proof.
  intros a b c Hab.
  transitivity
    (real_integral_between a b (fun x : R => c * (fun _ => 1%R) x)).
  - apply real_integral_extensional; intro x; ring.
  - (* The interval indicator is integrable even when its endpoints coincide.
       Use conversion for the Stdlib/library presentation of the constant one. *)
    rewrite real_integral_between_scale by apply real_integrable_between_one.
    f_equal; exact (real_integral_between_one a b Hab).
Qed.

Lemma real_integral_above_scale :
  forall (a c : R) (f : R -> R),
    real_integrable (fun x => real_indicator (a <= x)%R * f x) ->
    real_integral_above a (fun x => c * f x) =
      (c * real_integral_above a f)%R.
Proof.
  intros a c f Hf.
  unfold real_integral_above.
  transitivity
    (real_integral (fun x => c * (real_indicator (a <= x)%R * f x))).
  - apply real_integral_extensional; intro x; ring.
  - apply real_integral_scale; assumption.
Qed.

Lemma real_integral_split_three :
  forall (f : R -> R) (a b : R),
    (a <= b)%R ->
    real_integrable (fun x => real_indicator (x < a)%R * f x) ->
    real_integrable (fun x => real_indicator (a <= x < b)%R * f x) ->
    real_integrable (fun x => real_indicator (b <= x)%R * f x) ->
    real_integral f =
      (real_integral_below a f +
       real_integral_between a b f +
       real_integral_above b f)%R.
Proof.
  intros f a b Hab Hbelow Hbetween Habove.
  unfold real_integral_below, real_integral_between,
    real_integral_above.
  transitivity
    (real_integral
      (fun x =>
        real_indicator (x < a)%R * f x +
        (real_indicator (a <= x < b)%R * f x +
         real_indicator (b <= x)%R * f x))).
  - apply real_integral_extensional.
    intro x.
    destruct (Rlt_dec x a) as [Hxa | Hnxa].
    + rewrite (real_indicator_true _ Hxa).
      rewrite (real_indicator_false (a <= x < b)%R) by lra.
      rewrite (real_indicator_false (b <= x)%R) by lra.
      ring.
    + destruct (Rlt_dec x b) as [Hxb | Hnxb].
      * rewrite (real_indicator_false (x < a)%R) by lra.
        rewrite (real_indicator_true (a <= x < b)%R) by lra.
        rewrite (real_indicator_false (b <= x)%R) by lra.
        ring.
      * rewrite (real_indicator_false (x < a)%R) by lra.
        rewrite (real_indicator_false (a <= x < b)%R) by lra.
        rewrite (real_indicator_true (b <= x)%R) by lra.
        ring.
  - rewrite real_integral_add by (auto using real_integrable_add).
    rewrite real_integral_add by assumption.
    ring.
Qed.

(** Closed forms for the exponential functions needed below. *)
Axiom real_integral_exp_below :
  forall a k : R,
    (0 < k)%R ->
    real_integral_below a (fun x => exp (k * x)) =
      (exp (k * a) / k)%R.

Axiom real_integral_exp_between :
  forall a b k : R,
    (a <= b)%R ->
    k <> 0%R ->
    real_integral_between a b (fun x => exp (k * x)) =
      ((exp (k * b) - exp (k * a)) / k)%R.

Axiom real_integral_exp_above :
  forall a k : R,
    (k < 0)%R ->
    real_integral_above a (fun x => exp (k * x)) =
      (- exp (k * a) / k)%R.

(** The usual Laplace CDF, using the same [(location, scale)] convention as
    [Laplace] and [distribution_density]. *)
Definition laplace_cdf (location scale cutoff : R) : R :=
  if Rle_dec cutoff location
  then ((1 / 2) * exp ((cutoff - location) / scale))%R
  else (1 - (1 / 2) * exp (- (cutoff - location) / scale))%R.

(** Reusable closed forms derived from the exponential-region laws above.
    They are stated at the raw density level so later examples need not expose
    [Distribution] or a program state. *)
Lemma laplace_integral_left_below :
  forall location scale cutoff : R,
    (0 < scale)%R ->
    (cutoff <= location)%R ->
    real_integral_below cutoff
      (fun z =>
        (1 / (2 * scale)) *
          exp (- Rabs (z - location) / scale)) =
      ((1 / 2) * exp ((cutoff - location) / scale))%R.
Proof.
  intros location scale cutoff Hscale Hcutoff.
  transitivity
    (real_integral_below cutoff
      (fun z =>
        ((1 / (2 * scale)) * exp (- location / scale)) *
          exp ((1 / scale) * z))).
  - unfold real_integral_below.
    apply real_integral_extensional.
    intro z.
    destruct (Rlt_dec z cutoff) as [Hz | Hnz].
    + rewrite (real_indicator_true _ Hz).
      rewrite (Rabs_left (z - location)) by lra.
      assert (Hexp :
        (exp (- - (z - location) / scale) =
          exp (- location / scale) * exp ((1 / scale) * z))%R).
      {
        rewrite <- exp_plus.
        f_equal; field; lra.
      }
      rewrite Hexp; ring.
    + rewrite (real_indicator_false (z < cutoff)%R) by exact Hnz.
      ring.
  - rewrite real_integral_below_scale by
      (apply real_integrable_exp_below; apply Rdiv_lt_0_compat; lra).
    rewrite (real_integral_exp_below cutoff (1 / scale)).
    + assert (Hexp :
        (exp (- location / scale) * exp ((1 / scale) * cutoff) =
          exp ((cutoff - location) / scale))%R).
      {
        rewrite <- exp_plus.
        f_equal; field; lra.
      }
      rewrite <- Hexp.
      field; lra.
    + apply Rdiv_lt_0_compat; lra.
Qed.

Lemma laplace_integral_right_between :
  forall location scale cutoff : R,
    (0 < scale)%R ->
    (location <= cutoff)%R ->
    real_integral_between location cutoff
      (fun z =>
        (1 / (2 * scale)) *
          exp (- Rabs (z - location) / scale)) =
      ((1 / 2) *
        (1 - exp (- (cutoff - location) / scale)))%R.
Proof.
  intros location scale cutoff Hscale Hcutoff.
  transitivity
    (real_integral_between location cutoff
      (fun z =>
        ((1 / (2 * scale)) * exp (location / scale)) *
          exp ((- 1 / scale) * z))).
  - unfold real_integral_between.
    apply real_integral_extensional.
    intro z.
    (** Split the interval event using the general indicator interface. *)
    destruct (boolp.pselect (location <= z < cutoff)%R)
      as [Hz | Hnz].
    + rewrite (real_indicator_true _ Hz).
      rewrite (Rabs_right (z - location)) by lra.
      assert (Hexp :
        (exp (- (z - location) / scale) =
          exp (location / scale) * exp ((- 1 / scale) * z))%R).
      {
        rewrite <- exp_plus.
        f_equal; field; lra.
      }
      rewrite Hexp; ring.
    + rewrite (real_indicator_false (location <= z < cutoff)%R) by
        exact Hnz.
      ring.
  - rewrite real_integral_between_scale by apply real_integrable_exp_between.
    rewrite (real_integral_exp_between location cutoff (- 1 / scale)).
    2: exact Hcutoff.
    2: unfold Rdiv; apply Rmult_integral_contrapositive_currified;
       [lra | apply Rinv_neq_0_compat; lra].
    assert (Hexp_cutoff :
      (exp (location / scale) * exp ((- 1 / scale) * cutoff) =
        exp (- (cutoff - location) / scale))%R).
    {
      rewrite <- exp_plus.
      f_equal; field; lra.
    }
    assert (Hexp_location :
      (exp (location / scale) * exp ((- 1 / scale) * location) = 1)%R).
    {
      rewrite <- exp_plus.
      replace (location / scale + -1 / scale * location)%R with 0%R by
        (field; lra).
      apply exp_0.
    }
    transitivity
      (((1 / (2 * scale)) *
        (exp (location / scale) * exp ((- 1 / scale) * cutoff) -
         exp (location / scale) * exp ((- 1 / scale) * location))) /
        (- 1 / scale))%R.
    + field; lra.
    + rewrite Hexp_cutoff, Hexp_location.
      field; lra.
Qed.

Lemma laplace_integral_left_between :
  forall location scale cutoff : R,
    (0 < scale)%R ->
    (cutoff <= location)%R ->
    real_integral_between cutoff location
      (fun z =>
        (1 / (2 * scale)) *
          exp (- Rabs (z - location) / scale)) =
      ((1 / 2) *
        (1 - exp ((cutoff - location) / scale)))%R.
Proof.
  intros location scale cutoff Hscale Hcutoff.
  transitivity
    (real_integral_between cutoff location
      (fun z =>
        ((1 / (2 * scale)) * exp (- location / scale)) *
          exp ((1 / scale) * z))).
  - unfold real_integral_between.
    apply real_integral_extensional.
    intro z.
    (** Split the interval event using the general indicator interface. *)
    destruct (boolp.pselect (cutoff <= z < location)%R)
      as [Hz | Hnz].
    + rewrite (real_indicator_true _ Hz).
      rewrite (Rabs_left (z - location)) by lra.
      assert (Hexp :
        (exp (- - (z - location) / scale) =
          exp (- location / scale) * exp ((1 / scale) * z))%R).
      {
        rewrite <- exp_plus.
        f_equal; field; lra.
      }
      rewrite Hexp; ring.
    + rewrite (real_indicator_false (cutoff <= z < location)%R) by
        exact Hnz.
      ring.
  - rewrite real_integral_between_scale by apply real_integrable_exp_between.
    rewrite (real_integral_exp_between cutoff location (1 / scale)).
    2: exact Hcutoff.
    2: unfold Rdiv; apply Rmult_integral_contrapositive_currified;
       [lra | apply Rinv_neq_0_compat; lra].
    assert (Hexp_cutoff :
      (exp (- location / scale) * exp ((1 / scale) * cutoff) =
        exp ((cutoff - location) / scale))%R).
    {
      rewrite <- exp_plus.
      f_equal; field; lra.
    }
    assert (Hexp_location :
      (exp (- location / scale) * exp ((1 / scale) * location) = 1)%R).
    {
      rewrite <- exp_plus.
      replace (- location / scale + 1 / scale * location)%R with 0%R by
        (field; lra).
      apply exp_0.
    }
    transitivity
      (((1 / (2 * scale)) *
        (exp (- location / scale) * exp ((1 / scale) * location) -
         exp (- location / scale) * exp ((1 / scale) * cutoff))) /
        (1 / scale))%R.
    + field; lra.
    + rewrite Hexp_location, Hexp_cutoff.
      field; lra.
Qed.

Lemma laplace_integral_right_above :
  forall location scale cutoff : R,
    (0 < scale)%R ->
    (location <= cutoff)%R ->
    real_integral_above cutoff
      (fun z =>
        (1 / (2 * scale)) *
          exp (- Rabs (z - location) / scale)) =
      ((1 / 2) * exp (- (cutoff - location) / scale))%R.
Proof.
  intros location scale cutoff Hscale Hcutoff.
  transitivity
    (real_integral_above cutoff
      (fun z =>
        ((1 / (2 * scale)) * exp (location / scale)) *
          exp ((- 1 / scale) * z))).
  - unfold real_integral_above.
    apply real_integral_extensional.
    intro z.
    destruct (Rle_dec cutoff z) as [Hz | Hnz].
    + rewrite (real_indicator_true _ Hz).
      rewrite (Rabs_right (z - location)) by lra.
      assert (Hexp :
        (exp (- (z - location) / scale) =
          exp (location / scale) * exp ((- 1 / scale) * z))%R).
      {
        rewrite <- exp_plus.
        f_equal; field; lra.
      }
      rewrite Hexp; ring.
    + rewrite (real_indicator_false (cutoff <= z)%R) by exact Hnz.
      ring.
  - rewrite real_integral_above_scale by
      (apply real_integrable_exp_above;
       assert (0 < / scale)%R by (apply Rinv_0_lt_compat; lra);
       unfold Rdiv; nra).
    rewrite (real_integral_exp_above cutoff (- 1 / scale)).
    2: {
      replace (- 1 / scale)%R with (- (1 / scale))%R by
        (field; lra).
      apply Ropp_lt_gt_0_contravar.
      apply Rdiv_lt_0_compat; lra.
    }
    assert (Hexp :
      (exp (location / scale) * exp ((- 1 / scale) * cutoff) =
        exp (- (cutoff - location) / scale))%R).
    {
      rewrite <- exp_plus.
      f_equal; field; lra.
    }
    transitivity
      ((1 / (2 * scale)) *
        (exp (location / scale) * exp ((- 1 / scale) * cutoff)) *
        scale)%R.
    + field; lra.
    + rewrite Hexp.
      field; lra.
Qed.

Lemma laplace_integral_strict_cdf :
  forall location scale cutoff : R,
    (0 < scale)%R ->
    real_integral
      (fun z =>
        ((1 / (2 * scale)) *
          exp (- Rabs (z - location) / scale)) *
        real_indicator (z < cutoff)%R) =
      laplace_cdf location scale cutoff.
Proof.
  intros location scale cutoff Hscale.
  unfold laplace_cdf.
  destruct (Rle_dec cutoff location) as [Hleft | Hright].
  - transitivity
      (real_integral_below cutoff
        (fun z =>
          (1 / (2 * scale)) *
            exp (- Rabs (z - location) / scale))).
    + unfold real_integral_below.
      apply real_integral_extensional; intro z; ring.
    + apply laplace_integral_left_below; assumption.
  - transitivity
      (real_integral_below location
        (fun z =>
          (1 / (2 * scale)) *
            exp (- Rabs (z - location) / scale)) +
       real_integral_between location cutoff
        (fun z =>
          (1 / (2 * scale)) *
            exp (- Rabs (z - location) / scale)))%R.
    + unfold real_integral_below, real_integral_between.
      (* Both pieces are measurable restrictions of a normalized density. *)
      rewrite <- real_integral_add by
        (apply real_integrable_mask;
         [solve [apply real_measurable_below | apply real_measurable_between |
                 apply real_measurable_above] |
          apply real_integrable_laplace; assumption]).
      apply real_integral_extensional.
      intro z.
      destruct (Rlt_dec z location) as [Hzl | Hnzl].
      * rewrite (real_indicator_true (z < cutoff)%R) by lra.
        rewrite (real_indicator_true (z < location)%R) by exact Hzl.
        rewrite (real_indicator_false (location <= z < cutoff)%R) by lra.
        ring.
      * destruct (Rlt_dec z cutoff) as [Hzc | Hnzc].
        -- rewrite (real_indicator_true (z < cutoff)%R) by exact Hzc.
           rewrite (real_indicator_false (z < location)%R) by exact Hnzl.
           rewrite (real_indicator_true (location <= z < cutoff)%R) by lra.
           ring.
        -- rewrite (real_indicator_false (z < cutoff)%R) by exact Hnzc.
           rewrite (real_indicator_false (z < location)%R) by lra.
           rewrite (real_indicator_false (location <= z < cutoff)%R) by lra.
           ring.
    + rewrite (laplace_integral_left_below location scale location Hscale)
        by lra.
      rewrite (laplace_integral_right_between location scale cutoff Hscale)
        by lra.
      rewrite Rminus_diag.
      cbn.
      rewrite Rdiv_0_l by lra.
      rewrite exp_0.
      lra.
Qed.

Lemma laplace_integral_survival :
  forall location scale cutoff : R,
    (0 < scale)%R ->
    real_integral
      (fun z =>
        ((1 / (2 * scale)) *
          exp (- Rabs (z - location) / scale)) *
        real_indicator (cutoff <= z)%R) =
      (1 - laplace_cdf location scale cutoff)%R.
Proof.
  intros location scale cutoff Hscale.
  unfold laplace_cdf.
  destruct (Rle_dec cutoff location) as [Hleft | Hright].
  - transitivity
      (real_integral_between cutoff location
        (fun z =>
          (1 / (2 * scale)) *
            exp (- Rabs (z - location) / scale)) +
       real_integral_above location
        (fun z =>
          (1 / (2 * scale)) *
            exp (- Rabs (z - location) / scale)))%R.
    + unfold real_integral_between, real_integral_above.
      (* Both pieces are measurable restrictions of a normalized density. *)
      rewrite <- real_integral_add by
        (apply real_integrable_mask;
         [solve [apply real_measurable_below | apply real_measurable_between |
                 apply real_measurable_above] |
          apply real_integrable_laplace; assumption]).
      apply real_integral_extensional.
      intro z.
      destruct (Rlt_dec z location) as [Hzl | Hnzl].
      * destruct (Rle_dec cutoff z) as [Hcz | Hncz].
        -- rewrite (real_indicator_true (cutoff <= z)%R) by exact Hcz.
           rewrite (real_indicator_true (cutoff <= z < location)%R) by
             exact (conj Hcz Hzl).
           rewrite (real_indicator_false (location <= z)%R) by lra.
           ring.
        -- rewrite (real_indicator_false (cutoff <= z)%R) by exact Hncz.
           rewrite (real_indicator_false (cutoff <= z < location)%R) by lra.
           rewrite (real_indicator_false (location <= z)%R) by lra.
           ring.
      * rewrite (real_indicator_true (cutoff <= z)%R) by lra.
        rewrite (real_indicator_false (cutoff <= z < location)%R) by lra.
        rewrite (real_indicator_true (location <= z)%R) by lra.
        ring.
    + rewrite (laplace_integral_left_between location scale cutoff Hscale)
        by lra.
      rewrite (laplace_integral_right_above location scale location Hscale)
        by lra.
      rewrite Rminus_diag.
      cbn.
      rewrite Ropp_0.
      rewrite Rdiv_0_l by lra.
      rewrite exp_0.
      lra.
  - transitivity
      (real_integral_above cutoff
        (fun z =>
          (1 / (2 * scale)) *
            exp (- Rabs (z - location) / scale))).
    + unfold real_integral_above.
      apply real_integral_extensional; intro z; ring.
    + rewrite (laplace_integral_right_above location scale cutoff Hscale)
        by lra.
      ring.
Qed.

(** This small tactic discharges only concrete regional integrability goals:
    finite sums, scalar multiples, interval constants and exponential tails. *)
Ltac region_integrable :=
  first [assumption
  | apply real_integrable_exp_below; lra
  | apply real_integrable_exp_above; lra
  | apply real_integrable_exp_between
  | apply real_integrable_between_constant
  | apply real_integrable_mask_add; region_integrable
  | apply real_integrable_mask_scale; region_integrable].
