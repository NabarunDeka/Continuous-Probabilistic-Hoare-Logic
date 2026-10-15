(**
  AltExpLaplaceFacts.v -- density-integral facts used by
  LaplaceFromExponential.v.  No Hoare triple appears here.

  For [0 < b] and every cutoff [t], an exponential(1/b) variate [W] and a
  Laplace(0,b) variate [L] satisfy

      P(W < t) + P(-W < t) = 2 * P(L < t).
*)

From Stdlib Require Import Reals Lra.
Require Import MeasureIntegration CPHL.
Require Import CPHLFacts.CalculationFacts CPHLFacts.RealIntegrationFacts.
Require Import CPHLFacts.ExponentialIntegrals.
Require Import CdfLibraryFacts CdfAssertions.

Open Scope R_scope.

Section ExpLaplace.

Variable b : R.
Hypothesis Hb : 0 < b.

Let a : R := / b.

Lemma altexp_a_pos : 0 < a.
Proof. unfold a; apply Rinv_0_lt_compat; exact Hb. Qed.

(** The exponential density, masked by a measurable event, is integrable. *)
Lemma altexp_density_integrable : real_integrable (exp_density a).
Proof.
  pose proof altexp_a_pos as Ha.
  eapply real_integrable_ext with
    (f := fun z => a * (real_indicator (0 <= z) * exp (- a * z))).
  - intro z; unfold exp_density; ring.
  - apply real_integrable_scale, real_integrable_exp_above; lra.
Qed.

Lemma altexp_density_total : real_integral (exp_density a) = 1.
Proof.
  pose proof altexp_a_pos as Ha.
  transitivity (real_integral (fun z => exp_density a z * real_indicator (0 <= z))).
  - apply real_integral_extensional; intro z; unfold exp_density.
    destruct (Rle_dec 0 z) as [Hz | Hz].
    + rewrite (real_indicator_true _ Hz); ring.
    + rewrite (real_indicator_false _ Hz); ring.
  - rewrite exp_above_closed by lra.
    replace (- a * 0) with 0 by ring; apply exp_0.
Qed.

Lemma altexp_density_zero_neg : forall z, z < 0 -> exp_density a z = 0.
Proof.
  intros z Hz; unfold exp_density.
  rewrite (real_indicator_false (0 <= z)) by lra; ring.
Qed.

(** Lower tail of the exponential, [P(W < t)]. *)
Definition altexp_below (t : R) : R :=
  real_integral (fun r => exp_density a r * real_indicator (r < t)).

(** Reflected tail, [P(-W < t)], written with the event exactly as the
    assertion [(-1) * w < t] unfolds. *)
Definition altexp_reflected (t : R) : R :=
  real_integral (fun r => exp_density a r * real_indicator (~ (t <= -1 * r))).

Lemma altexp_below_nonpos : forall t, t <= 0 -> altexp_below t = 0.
Proof.
  intros t Ht; unfold altexp_below.
  rewrite <- real_integral_zero.
  apply real_integral_extensional; intro r.
  destruct (Rlt_dec r t) as [Hr | Hr].
  - rewrite altexp_density_zero_neg by lra; ring.
  - rewrite (real_indicator_false _ Hr); ring.
Qed.

Lemma altexp_below_pos : forall t, 0 <= t -> altexp_below t = 1 - exp (- a * t).
Proof.
  intros t Ht; pose proof altexp_a_pos as Ha; unfold altexp_below.
  rewrite <- (exp_above_closed a t Ha Ht), <- altexp_density_total.
  transitivity
    (real_integral (fun r => exp_density a r +
                            (-1) * (exp_density a r * real_indicator (t <= r)))).
  - apply real_integral_extensional; intro r.
    destruct (Rlt_dec r t) as [Hr | Hr].
    + rewrite (real_indicator_true _ Hr).
      rewrite (real_indicator_false (t <= r)) by lra; ring.
    + rewrite (real_indicator_false _ Hr).
      rewrite (real_indicator_true (t <= r)) by lra; ring.
  - rewrite real_integral_add.
    + rewrite real_integral_scale; [ring |].
      apply real_integrable_mask_right;
        [apply real_measurable_above | exact altexp_density_integrable].
    + exact altexp_density_integrable.
    + apply real_integrable_scale, real_integrable_mask_right;
        [apply real_measurable_above | exact altexp_density_integrable].
Qed.

Lemma altexp_reflected_pos : forall t, 0 < t -> altexp_reflected t = 1.
Proof.
  intros t Ht; unfold altexp_reflected.
  rewrite <- altexp_density_total.
  apply real_integral_extensional; intro r.
  destruct (Rle_dec 0 r) as [Hr | Hr].
  - rewrite (real_indicator_true (~ (t <= -1 * r))) by lra; ring.
  - rewrite altexp_density_zero_neg by lra; ring.
Qed.

Lemma altexp_reflected_nonpos : forall t, t <= 0 -> altexp_reflected t = exp (a * t).
Proof.
  intros t Ht; pose proof altexp_a_pos as Ha; unfold altexp_reflected.
  replace (exp (a * t)) with
    (real_integral (fun r => exp_density a r * real_indicator (- t <= r)) +
     (-1) * real_integral (fun r => real_indicator (r = - t) * exp_density a r)).
  - rewrite <- real_integral_scale
      by (apply real_integrable_mask;
          [apply real_measurable_point | exact altexp_density_integrable]).
    rewrite <- real_integral_add.
    + apply real_integral_extensional; intro r.
      destruct (Req_dec r (- t)) as [He | Hne].
      * rewrite (real_indicator_true (r = - t)) by exact He.
        rewrite (real_indicator_true (- t <= r)) by lra.
        rewrite (real_indicator_false (~ (t <= -1 * r))) by lra; ring.
      * rewrite (real_indicator_false (r = - t)) by exact Hne.
        destruct (Rlt_dec (- t) r) as [Hr | Hr].
        -- rewrite (real_indicator_true (- t <= r)) by lra.
           rewrite (real_indicator_true (~ (t <= -1 * r))) by lra; ring.
        -- rewrite (real_indicator_false (- t <= r)) by lra.
           rewrite (real_indicator_false (~ (t <= -1 * r))) by lra; ring.
    + apply real_integrable_mask_right;
        [apply real_measurable_above | exact altexp_density_integrable].
    + apply real_integrable_scale, real_integrable_mask;
        [apply real_measurable_point | exact altexp_density_integrable].
  - rewrite exp_above_closed by lra.
    rewrite real_integral_singleton_zero; change nmodule.Algebra.zero with 0%R.
    replace (- a * - t) with (a * t) by ring; ring.
Qed.

(** The Laplace lower tail below a nonpositive cutoff. *)
Lemma altexp_lap_below_nonpos :
  forall t, t <= 0 -> lap_below 0 b t = (1 / 2) * exp (a * t).
Proof.
  intros t Ht; pose proof altexp_a_pos as Ha; unfold lap_below, lap_density.
  transitivity
    (real_integral (fun z => (1 / (2 * b)) * (real_indicator (z < t) * exp (a * z)))).
  - apply real_integral_extensional; intro z.
    destruct (Rlt_dec z t) as [Hz | Hz].
    + rewrite (real_indicator_true _ Hz).
      rewrite Rminus_0_r, Rabs_left by lra.
      replace (- - z / b) with (a * z) by (unfold a; field; lra).
      ring.
    + rewrite (real_indicator_false _ Hz); ring.
  - rewrite real_integral_scale by (apply real_integrable_exp_below; exact Ha).
    change (real_integral (fun z => real_indicator (z < t) * exp (a * z)))
      with (real_integral_below t (fun z => exp (a * z))).
    rewrite real_integral_exp_below_proved by exact Ha.
    unfold a; field; lra.
Qed.

Lemma altexp_lap_below_pos :
  forall t, 0 <= t -> lap_below 0 b t = 1 - (1 / 2) * exp (- a * t).
Proof.
  intros t Ht.
  pose proof (lap_below_above 0 b Hb t) as H.
  rewrite (lap_above_closed b t Hb Ht) in H.
  replace (- a * t) with (- t / b) by (unfold a; field; lra).
  lra.
Qed.

(** The mixture identity. *)
Theorem altexp_mixture :
  forall t, altexp_below t + altexp_reflected t = 2 * lap_below 0 b t.
Proof.
  intro t.
  destruct (Rle_dec t 0) as [Ht | Ht].
  - rewrite altexp_below_nonpos, altexp_reflected_nonpos, altexp_lap_below_nonpos
      by exact Ht.
    field.
  - rewrite altexp_below_pos, altexp_reflected_pos, altexp_lap_below_pos by lra.
    field.
Qed.

End ExpLaplace.
