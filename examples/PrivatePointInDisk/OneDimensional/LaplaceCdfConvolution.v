(**
  LaplaceCdfConvolution.v -- analytic support, no program and no triple.

  [lcc_convolution_cdf] (for 0 < b), with [f_b] the centred Laplace density
  [lc_density] and [F_b = lap_atmost 0 b] its CDF (a density integral):

      INT  f_b(u) * F_b(u + t)  du  =  lcc_G b t

      lcc_G b t = (1/4) * (2 - t/b) * exp(t/b)            for t <= 0
                = 1 - (1/4) * (2 + t/b) * exp(-t/b)       for t >  0

  i.e. the CDF of [Y - X] for independent X, Y ~ Laplace(0, b).
  Axiom-free.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Require Import MeasureIntegration CPHL.
Require Import CPHLFacts.CalculationFacts.
Require Import CPHLFacts.ExponentialIntegrals.
Require Import CdfAssertions.
Require Import DiskLaplaceFacts.
Require Import LaplaceConvolution.

Open Scope R_scope.

(** * The two branches of the closed-form Laplace CDF [disk_F] *)

Lemma lcc_F_nonpos :
  forall b x : R, (x <= 0)%R -> disk_F b x = ((1 / 2) * exp (x / b))%R.
Proof. exact disk_F_nonpos. Qed.

Lemma lcc_F_pos :
  forall b x : R,
    (0 < x)%R -> disk_F b x = (1 - (1 / 2) * exp (- x / b))%R.
Proof.
  intros b x Hx; unfold disk_F.
  destruct (Rle_dec x 0) as [H | H]; [lra | reflexivity].
Qed.

Lemma lcc_F_nonneg :
  forall b x : R,
    (0 < b)%R -> (0 <= x)%R ->
    disk_F b x = (1 - (1 / 2) * exp (- x / b))%R.
Proof. exact disk_F_nonneg. Qed.

(** * One more region integral: an exponential over a bounded window *)

Lemma lcc_between_exp :
  forall m M k C : R,
    (m <= M)%R ->
    k <> 0%R ->
    real_integral (fun u => real_indicator (m <= u < M)%R * (C * exp (k * u))) =
    (C * ((exp (k * M) - exp (k * m)) / k))%R.
Proof.
  intros m M k C Hm Hk.
  rewrite <- (real_integral_exp_between_proved m M k Hm Hk).
  unfold real_integral_between.
  rewrite <- real_integral_scale by apply real_integrable_exp_between.
  apply real_integral_extensional; intro u; ring.
Qed.

Lemma lcc_region_minus :
  forall (P : R -> Prop) (A B : R -> R),
    real_integrable (fun u => real_indicator (P u) * A u) ->
    real_integrable (fun u => real_indicator (P u) * B u) ->
    real_integral (fun u => real_indicator (P u) * (A u - B u))%R =
    (real_integral (fun u => real_indicator (P u) * A u)
     - real_integral (fun u => real_indicator (P u) * B u))%R.
Proof.
  intros P A B HA HB.
  transitivity (real_integral (fun u => real_indicator (P u) * A u
                  + (-1) * (real_indicator (P u) * B u)))%R.
  - apply real_integral_extensional; intro u; ring.
  - rewrite real_integral_add, real_integral_scale; [ring | exact HB | exact HA |].
    exact (@ConcreteMeasure.integrable_scale _ RealIntegration.Space
             RealIntegration.lebesgue (-1) _ HB).
Qed.

(** * The answer *)

Definition lcc_G (b t : R) : R :=
  if Rle_dec t 0
  then ((1 / 4) * (2 - t / b) * exp (t / b))%R
  else (1 - (1 / 4) * (2 + t / b) * exp (- t / b))%R.

(** * The cumulative convolution *)

Lemma lcc_convolution_F :
  forall b t : R,
    (0 < b)%R ->
    real_integral (fun u => lc_density b u * disk_F b (u + t)) =
    lcc_G b t.
Proof.
  intros b t Hb.
  assert (Hb2 : (b <> 0)%R) by lra.
  assert (Hk : (0 < 2 / b)%R)
    by (unfold Rdiv; apply Rmult_lt_0_compat;
        [lra | apply Rinv_0_lt_compat; exact Hb]).
  assert (Hkn : (- (2 / b) < 0)%R) by lra.
  assert (Hk1 : (0 < 1 / b)%R)
    by (unfold Rdiv; apply Rmult_lt_0_compat;
        [lra | apply Rinv_0_lt_compat; exact Hb]).
  assert (Hk1n : (- (1 / b) < 0)%R) by lra.
  unfold lcc_G.
  destruct (Rle_dec t 0) as [Ht | Ht].
  - (* t <= 0 : breakpoints 0 then -t *)
    assert (Hmt : (0 <= - t)%R) by lra.
    rewrite (lc_split3 0 (- t) _
               (fun u => (((1 / (4 * b)) * exp (t / b))
                            * exp ((2 / b) * u)))
               (fun u => ((1 / (4 * b)) * exp (t / b)))
               (fun u => (((1 / (2 * b)) * exp ((- (1 / b)) * u))
                            - ((1 / (4 * b)) * exp (- t / b))
                              * exp ((- (2 / b)) * u))) Hmt).
    2:{ intro u; cbv beta.
        destruct (Rlt_dec u 0) as [Hu | Hu].
        - rewrite (real_indicator_true (u < 0)%R Hu).
          rewrite (lcc_F_nonpos b (u + t)) by lra.
          unfold lc_density.
          rewrite (Rabs_left u Hu).
          replace (- - u / b)%R with (u / b)%R by (field; exact Hb2).
          replace ((1 / (2 * b)) * exp (u / b) * ((1 / 2) * exp ((u + t) / b)))%R
            with ((1 / (4 * b)) * (exp (u / b) * exp ((u + t) / b)))%R
            by (field; exact Hb2).
          rewrite <- exp_plus.
          replace (u / b + (u + t) / b)%R with (t / b + 2 / b * u)%R
            by (field; exact Hb2).
          rewrite exp_plus; ring.
        - rewrite (real_indicator_false (u < 0)%R) by lra; ring. }
    2:{ intro u; cbv beta.
        destruct (Rle_dec 0 u) as [Hu1 | Hu1];
          [destruct (Rlt_dec u (- t)) as [Hu2 | Hu2] |].
        - rewrite (real_indicator_true (0 <= u < - t)%R (conj Hu1 Hu2)).
          rewrite (lcc_F_nonpos b (u + t)) by lra.
          unfold lc_density.
          rewrite (Rabs_pos_eq u Hu1).
          replace ((1 / (2 * b)) * exp (- u / b) * ((1 / 2) * exp ((u + t) / b)))%R
            with ((1 / (4 * b)) * (exp (- u / b) * exp ((u + t) / b)))%R
            by (field; exact Hb2).
          rewrite <- exp_plus.
          replace (- u / b + (u + t) / b)%R with (t / b)%R by (field; exact Hb2).
          ring.
        - rewrite (real_indicator_false (0 <= u < - t)%R)
            by (intros [_ Hc]; lra); ring.
        - rewrite (real_indicator_false (0 <= u < - t)%R)
            by (intros [Hc _]; lra); ring. }
    2:{ intro u; cbv beta.
        destruct (Rle_dec (- t) u) as [Hu | Hu].
        - rewrite (real_indicator_true (- t <= u)%R Hu).
          assert (Hup : (0 <= u)%R) by lra.
          rewrite (lcc_F_nonneg b (u + t) Hb) by lra.
          unfold lc_density.
          rewrite (Rabs_pos_eq u Hup).
          replace ((1 / (2 * b)) * exp (- u / b) * (1 - (1 / 2) * exp (- (u + t) / b)))%R
            with ((1 / (2 * b)) * exp (- u / b)
                  - (1 / (4 * b)) * (exp (- u / b) * exp (- (u + t) / b)))%R
            by (field; exact Hb2).
          rewrite <- exp_plus.
          replace (- u / b + - (u + t) / b)%R with (- t / b + - (2 / b) * u)%R
            by (field; exact Hb2).
          rewrite exp_plus.
          replace (- (1 / b) * u)%R with (- u / b)%R by (field; exact Hb2).
          ring.
        - rewrite (real_indicator_false (- t <= u)%R) by lra; ring. }
    2-4: lc_integrable.
    rewrite (lc_below_exp 0 (2 / b) _ Hk).
    rewrite (lc_between_const 0 (- t) _ Hmt).
    rewrite lcc_region_minus by lc_integrable.
    rewrite (lc_above_exp (- t) (- (1 / b)) _ Hk1n).
    rewrite (lc_above_exp (- t) (- (2 / b)) _ Hkn).
    replace (2 / b * 0)%R with 0%R by ring.
    rewrite exp_0.
    set (E := exp (t / b)).
    assert (HE : (0 < E)%R) by (unfold E; apply exp_pos).
    assert (HE0 : (E <> 0)%R) by (apply Rgt_not_eq; exact HE).
    assert (H1 : exp (- (1 / b) * - t) = E).
    { unfold E; f_equal; field; exact Hb2. }
    assert (H2 : exp (- t / b) = (/ E)%R).
    { unfold E; rewrite <- exp_Ropp; f_equal; field; exact Hb2. }
    assert (H3 : exp (- (2 / b) * - t) = (E * E)%R).
    { replace (- (2 / b) * - t)%R with (t / b + t / b)%R by (field; exact Hb2).
      rewrite exp_plus; reflexivity. }
    rewrite H1, H2, H3.
    field; repeat split; try lra; exact HE0.
  - (* t > 0 : breakpoints -t then 0 *)
    assert (Htp : (0 < t)%R) by lra.
    assert (Hmt : (- t <= 0)%R) by lra.
    rewrite (lc_split3 (- t) 0 _
               (fun u => (((1 / (4 * b)) * exp (t / b))
                            * exp ((2 / b) * u)))
               (fun u => (((1 / (2 * b)) * exp ((1 / b) * u))
                            - (1 / (4 * b)) * exp (- t / b)))
               (fun u => (((1 / (2 * b)) * exp ((- (1 / b)) * u))
                            - ((1 / (4 * b)) * exp (- t / b))
                              * exp ((- (2 / b)) * u))) Hmt).
    2:{ intro u; cbv beta.
        destruct (Rlt_dec u (- t)) as [Hu | Hu].
        - rewrite (real_indicator_true (u < - t)%R Hu).
          rewrite (lcc_F_nonpos b (u + t)) by lra.
          unfold lc_density.
          rewrite (Rabs_left u) by lra.
          replace (- - u / b)%R with (u / b)%R by (field; exact Hb2).
          replace ((1 / (2 * b)) * exp (u / b) * ((1 / 2) * exp ((u + t) / b)))%R
            with ((1 / (4 * b)) * (exp (u / b) * exp ((u + t) / b)))%R
            by (field; exact Hb2).
          rewrite <- exp_plus.
          replace (u / b + (u + t) / b)%R with (t / b + 2 / b * u)%R
            by (field; exact Hb2).
          rewrite exp_plus; ring.
        - rewrite (real_indicator_false (u < - t)%R) by lra; ring. }
    2:{ intro u; cbv beta.
        destruct (Rle_dec (- t) u) as [Hu1 | Hu1];
          [destruct (Rlt_dec u 0) as [Hu2 | Hu2] |].
        - rewrite (real_indicator_true (- t <= u < 0)%R (conj Hu1 Hu2)).
          rewrite (lcc_F_nonneg b (u + t) Hb) by lra.
          unfold lc_density.
          rewrite (Rabs_left u Hu2).
          replace (- - u / b)%R with (u / b)%R by (field; exact Hb2).
          replace ((1 / (2 * b)) * exp (u / b) * (1 - (1 / 2) * exp (- (u + t) / b)))%R
            with ((1 / (2 * b)) * exp (u / b)
                  - (1 / (4 * b)) * (exp (u / b) * exp (- (u + t) / b)))%R
            by (field; exact Hb2).
          rewrite <- exp_plus.
          replace (u / b + - (u + t) / b)%R with (- t / b)%R by (field; exact Hb2).
          replace (1 / b * u)%R with (u / b)%R by (field; exact Hb2).
          ring.
        - rewrite (real_indicator_false (- t <= u < 0)%R)
            by (intros [_ Hc]; lra); ring.
        - rewrite (real_indicator_false (- t <= u < 0)%R)
            by (intros [Hc _]; lra); ring. }
    2:{ intro u; cbv beta.
        destruct (Rle_dec 0 u) as [Hu | Hu].
        - rewrite (real_indicator_true (0 <= u)%R Hu).
          rewrite (lcc_F_pos b (u + t)) by lra.
          unfold lc_density.
          rewrite (Rabs_pos_eq u Hu).
          replace ((1 / (2 * b)) * exp (- u / b) * (1 - (1 / 2) * exp (- (u + t) / b)))%R
            with ((1 / (2 * b)) * exp (- u / b)
                  - (1 / (4 * b)) * (exp (- u / b) * exp (- (u + t) / b)))%R
            by (field; exact Hb2).
          rewrite <- exp_plus.
          replace (- u / b + - (u + t) / b)%R with (- t / b + - (2 / b) * u)%R
            by (field; exact Hb2).
          rewrite exp_plus.
          replace (- (1 / b) * u)%R with (- u / b)%R by (field; exact Hb2).
          ring.
        - rewrite (real_indicator_false (0 <= u)%R) by lra; ring. }
    2-4: lc_integrable.
    rewrite (lc_below_exp (- t) (2 / b) _ Hk).
    rewrite lcc_region_minus by lc_integrable.
    rewrite (lcc_between_exp (- t) 0 (1 / b) _ Hmt) by lra.
    rewrite (lc_between_const (- t) 0 _ Hmt).
    rewrite lcc_region_minus by lc_integrable.
    rewrite (lc_above_exp 0 (- (1 / b)) _ Hk1n).
    rewrite (lc_above_exp 0 (- (2 / b)) _ Hkn).
    replace (- (1 / b) * 0)%R with 0%R by ring.
    replace (- (2 / b) * 0)%R with 0%R by ring.
    replace (1 / b * 0)%R with 0%R by ring.
    rewrite !exp_0.
    set (E := exp (- t / b)).
    assert (HE : (0 < E)%R) by (unfold E; apply exp_pos).
    assert (HE0 : (E <> 0)%R) by (apply Rgt_not_eq; exact HE).
    assert (H1 : exp (2 / b * - t) = (E * E)%R).
    { replace (2 / b * - t)%R with (- t / b + - t / b)%R by (field; exact Hb2).
      rewrite exp_plus; reflexivity. }
    assert (H2 : exp (t / b) = (/ E)%R).
    { unfold E; rewrite <- exp_Ropp; f_equal; field; exact Hb2. }
    assert (H3 : exp (1 / b * - t) = E).
    { unfold E; f_equal; field; exact Hb2. }
    rewrite H1, H2, H3.
    field; repeat split; try lra; exact HE0.
Qed.

(** The same statement with the CDF written as a density integral. *)
Theorem lcc_convolution_cdf :
  forall b t : R,
    (0 < b)%R ->
    real_integral (fun u => lc_density b u * lap_atmost 0 b (u + t)) =
    lcc_G b t.
Proof.
  intros b t Hb.
  rewrite <- (lcc_convolution_F b t Hb).
  apply real_integral_extensional; intro u.
  rewrite (disk_lap_atmost_closed 0 b (u + t) Hb).
  rewrite Rminus_0_r; reflexivity.
Qed.
