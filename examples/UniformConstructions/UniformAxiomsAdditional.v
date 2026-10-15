(**
  UniformAxiomsAdditional.v

  No program and no triple: real-integral facts for the uniform
  distribution used by UniformRejectionSampling.v, TriangularRejection.v
  and MaxOfTwoUniforms.v.  All are proved lemmas (no axioms).
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Require Import CPHL.
Require Import CPHLFacts.CalculationFacts.
Require Import UniformLinearIntegral.

Open Scope R_scope.
Local Open Scope cphl_scope.

(** * Interval laws (formerly axioms, now proved) *)

Lemma real_integral_between_length :
  forall a b : R,
    (a <= b)%R ->
    real_integral_between a b (fun _ => 1%R) = (b - a)%R.
Proof. intros a b Hab; exact (real_integral_between_one a b Hab). Qed.

Lemma real_integral_point_null :
  forall (c : R) (f : R -> R),
    real_integral (fun z => real_indicator (z = c)%R * f z) = 0%R.
Proof. intros c f; exact (real_integral_singleton_zero c f). Qed.

Lemma real_integral_between_linear :
  forall a b : R,
    (a <= b)%R ->
    real_integral_between a b (fun x => x) = ((b * b - a * a) / 2)%R.
Proof. intros a b Hab; exact (real_integral_between_linear_proved a b Hab). Qed.

Lemma real_integral_indicator_interval :
  forall a b : R,
    (a <= b)%R ->
    real_integral (fun z => real_indicator (a <= z < b)%R) = (b - a)%R.
Proof.
  intros a b Hab.
  rewrite <- (real_integral_between_length a b Hab).
  unfold real_integral_between.
  apply real_integral_extensional; intro z; ring.
Qed.

Lemma real_integral_indicator_linear :
  forall a b : R,
    (a <= b)%R ->
    real_integral (fun z => real_indicator (a <= z < b)%R * z) =
    ((b * b - a * a) / 2)%R.
Proof.
  intros a b Hab.
  rewrite <- (real_integral_between_linear a b Hab).
  reflexivity.
Qed.

(** * Integrability of interval indicators *)

Lemma real_integrable_closed_const :
  forall a b c : R,
    real_integrable (fun z => real_indicator (a <= z <= b)%R * c).
Proof.
  intros a b c.
  apply real_integrable_ext with
    (f := fun z => (real_indicator (a <= z < b + 1)%R * c) *
                   real_indicator (z <= b)%R).
  - intro z.
    destruct (Rle_dec z b) as [Hz | Hz].
    + rewrite (real_indicator_true (z <= b)%R Hz).
      destruct (Rle_dec a z) as [Ha | Ha].
      * rewrite (real_indicator_true (a <= z < b + 1)%R) by lra.
        rewrite (real_indicator_true (a <= z <= b)%R) by lra; ring.
      * rewrite (real_indicator_false (a <= z < b + 1)%R) by lra.
        rewrite (real_indicator_false (a <= z <= b)%R) by lra; ring.
    + rewrite (real_indicator_false (z <= b)%R Hz).
      rewrite (real_indicator_false (a <= z <= b)%R) by lra; ring.
  - apply real_integrable_mask_right;
      [apply real_measurable_atmost | apply real_integrable_between_constant].
Qed.

Lemma real_integrable_open_affine :
  forall a b c d : R,
    real_integrable (fun z => real_indicator (a <= z < b)%R * (c + d * z)).
Proof.
  intros a b c d.
  apply real_integrable_mask_add.
  - apply real_integrable_between_constant.
  - apply real_integrable_mask_scale, real_integrable_between_id.
Qed.

(** * Closed forms for masked constants and affine functions *)

Lemma real_integral_open_const :
  forall a b c : R,
    (a <= b)%R ->
    real_integral (fun z => real_indicator (a <= z < b)%R * c) = (c * (b - a))%R.
Proof.
  intros a b c Hab.
  rewrite (real_integral_extensional _
             (fun z => c * (real_indicator (a <= z < b)%R * 1))) by (intro; ring).
  rewrite real_integral_scale by apply real_integrable_between_one.
  rewrite <- (real_integral_between_length a b Hab); reflexivity.
Qed.

Lemma real_integral_closed_const :
  forall a b c : R,
    (a <= b)%R ->
    real_integral (fun z => real_indicator (a <= z <= b)%R * c) = (c * (b - a))%R.
Proof.
  intros a b c Hab.
  rewrite (real_integral_extensional _
             (fun z => c * (real_indicator (a <= z <= b)%R * 1))) by (intro; ring).
  rewrite real_integral_scale by apply real_integrable_closed_const.
  rewrite (real_integral_extensional _
             (fun z => real_indicator (a <= z /\ z <= b)%R)) by (intro; ring).
  rewrite (real_integral_closed_between_one a b Hab); reflexivity.
Qed.

Lemma real_integral_open_affine :
  forall a b c d : R,
    (a <= b)%R ->
    real_integral (fun z => real_indicator (a <= z < b)%R * (c + d * z)) =
    (c * (b - a) + d * ((b * b - a * a) / 2))%R.
Proof.
  intros a b c d Hab.
  rewrite (real_integral_extensional _
             (fun z => real_indicator (a <= z < b)%R * c +
                       d * (real_indicator (a <= z < b)%R * z))) by (intro; ring).
  rewrite real_integral_add.
  - rewrite real_integral_scale by apply real_integrable_between_id.
    rewrite (real_integral_open_const a b c Hab).
    rewrite (real_integral_indicator_linear a b Hab); reflexivity.
  - apply real_integrable_between_constant.
  - apply real_integrable_scale, real_integrable_between_id.
Qed.

Lemma real_integral_minus :
  forall f g : R -> R,
    real_integrable f -> real_integrable g ->
    real_integral (fun x => (f x - g x)%R) =
    (real_integral f - real_integral g)%R.
Proof.
  intros f g Hf Hg.
  rewrite (real_integral_extensional _ (fun x => f x + (-1) * g x))
    by (intro; ring).
  rewrite real_integral_add, real_integral_scale;
    [ring | exact Hg | exact Hf | apply real_integrable_scale; exact Hg].
Qed.

(** * The uniform density and CDF *)

Definition uniform_density_R (l u z : R) : R :=
  (real_indicator (l <= z <= u)%R / (u - l))%R.

Definition uniform_cdf (l u t : R) : R :=
  if Rle_dec t l then 0%R
  else if Rle_dec u t then 1%R
  else ((t - l) / (u - l))%R.

Lemma uniform_integral_strict_cdf :
  forall l u t : R,
    (l < u)%R ->
    real_integral
      (fun z => uniform_density_R l u z * real_indicator (z < t)%R) =
    uniform_cdf l u t.
Proof.
  intros l u t Hlu.
  unfold uniform_cdf, uniform_density_R, Rdiv.
  destruct (Rle_dec t l) as [Htl | Htl].
  - rewrite (real_integral_extensional _ (fun _ => 0%R)).
    + apply real_integral_zero.
    + intro z.
      destruct (Rlt_dec z t) as [Hzt | Hzt].
      * rewrite (real_indicator_false (l <= z <= u)%R) by lra; ring.
      * rewrite (real_indicator_false (z < t)%R) by lra; ring.
  - destruct (Rle_dec u t) as [Hut | Hut].
    + destruct (Rle_dec t u) as [Htu | Htu].
      * (* t = u: the endpoint is excluded but has no mass *)
        rewrite (real_integral_extensional _
                   (fun z => real_indicator (l <= z < u)%R * / (u - l))).
        -- rewrite real_integral_open_const by lra; field; lra.
        -- intro z.
           destruct (Rlt_dec z u) as [Hz | Hz].
           ++ rewrite (real_indicator_true (z < t)%R) by lra.
              destruct (Rle_dec l z) as [Hl | Hl].
              ** rewrite (real_indicator_true (l <= z <= u)%R) by lra.
                 rewrite (real_indicator_true (l <= z < u)%R) by lra; ring.
              ** rewrite (real_indicator_false (l <= z <= u)%R) by lra.
                 rewrite (real_indicator_false (l <= z < u)%R) by lra; ring.
           ++ rewrite (real_indicator_false (z < t)%R) by lra.
              rewrite (real_indicator_false (l <= z < u)%R) by lra; ring.
      * rewrite (real_integral_extensional _
                   (fun z => real_indicator (l <= z <= u)%R * / (u - l))).
        -- rewrite real_integral_closed_const by lra; field; lra.
        -- intro z.
           destruct (Rle_dec z u) as [Hz | Hz].
           ++ rewrite (real_indicator_true (z < t)%R) by lra; ring.
           ++ rewrite (real_indicator_false (l <= z <= u)%R) by lra; ring.
    + rewrite (real_integral_extensional _
                 (fun z => real_indicator (l <= z < t)%R * / (u - l))).
      * rewrite real_integral_open_const by lra; field; lra.
      * intro z.
        destruct (Rlt_dec z t) as [Hzt | Hzt].
        -- rewrite (real_indicator_true (z < t)%R Hzt).
           destruct (Rle_dec l z) as [Hlz | Hlz].
           ++ rewrite (real_indicator_true (l <= z <= u)%R) by lra.
              rewrite (real_indicator_true (l <= z < t)%R) by lra; ring.
           ++ rewrite (real_indicator_false (l <= z <= u)%R) by lra.
              rewrite (real_indicator_false (l <= z < t)%R) by lra; ring.
        -- rewrite (real_indicator_false (z < t)%R) by lra.
           rewrite (real_indicator_false (l <= z < t)%R) by lra; ring.
Qed.

Lemma uniform_density_total :
  forall l u : R,
    (l < u)%R ->
    real_integral (uniform_density_R l u) = 1%R.
Proof.
  intros l u Hlu.
  unfold uniform_density_R, Rdiv.
  rewrite real_integral_closed_const by lra; field; lra.
Qed.

Lemma uniform_density_integrable :
  forall l u : R, real_integrable (uniform_density_R l u).
Proof.
  intros l u; unfold uniform_density_R, Rdiv.
  apply real_integrable_closed_const.
Qed.

Lemma uniform_integral_survival :
  forall l u t : R,
    (l < u)%R ->
    real_integral
      (fun z => uniform_density_R l u z * real_indicator (t <= z)%R) =
    (1 - uniform_cdf l u t)%R.
Proof.
  intros l u t Hlu.
  rewrite <- (uniform_density_total l u Hlu).
  rewrite <- (uniform_integral_strict_cdf l u t Hlu).
  rewrite <- real_integral_minus.
  - apply real_integral_extensional; intro z.
    destruct (Rlt_dec z t) as [Hz | Hz].
    + rewrite (real_indicator_true (z < t)%R Hz).
      rewrite (real_indicator_false (t <= z)%R) by lra; ring.
    + rewrite (real_indicator_false (z < t)%R) by lra.
      rewrite (real_indicator_true (t <= z)%R) by lra; ring.
  - apply uniform_density_integrable.
  - apply real_integrable_mask_right;
      [apply real_measurable_below | apply uniform_density_integrable].
Qed.

Lemma uniform_cdf_bounds :
  forall l u t : R,
    (l < u)%R -> (0 <= uniform_cdf l u t <= 1)%R.
Proof.
  intros l u t Hlu.
  unfold uniform_cdf.
  destruct (Rle_dec t l) as [H | H]; [lra |].
  destruct (Rle_dec u t) as [H' | H']; [lra |].
  assert (Hval : ((t - l) / (u - l) * (u - l))%R = (t - l)%R)
    by (field; lra).
  split.
  - apply Rmult_le_reg_r with (r := (u - l)%R); [lra |].
    rewrite Hval; lra.
  - apply Rmult_le_reg_r with (r := (u - l)%R); [lra |].
    rewrite Hval; lra.
Qed.

Lemma uniform_cdf_unit :
  forall t : R, (0 <= t)%R -> (t <= 1)%R -> uniform_cdf 0 1 t = t.
Proof.
  intros t H0 H1.
  unfold uniform_cdf.
  destruct (Rle_dec t 0) as [H | H].
  - assert (Ht : t = 0%R) by lra; subst t; reflexivity.
  - destruct (Rle_dec 1 t) as [H' | H'].
    + assert (Ht : t = 1%R) by lra; subst t; reflexivity.
    + field.
Qed.

(** * The unit uniform as a kernel expectation *)

Lemma q_eval_unit_uniform :
  forall (x : RealProgramVar) (q : PConstruct) (v : state),
    q_eval (QIntegral x <{ uniform(0, 1) }> q) v =
    real_integral
      (fun z => real_indicator (0 <= z <= 1)%R * q_eval q (update_real v x z)).
Proof.
  intros x q v.
  rewrite q_integral_density by (cbn [distribution_valid term_eval]; lra).
  apply real_integral_extensional; intro z.
  cbn [distribution_density term_eval].
  unfold Rdiv; rewrite Rminus_0_r, Rinv_1; ring.
Qed.
