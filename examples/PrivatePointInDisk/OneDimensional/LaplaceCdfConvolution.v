(**
  LaplaceCdfConvolution.v -- the CUMULATIVE law of a sum of two independent
  Laplace variables.

  NO TRIPLE.  Analytic support for OneDimPoints.v, in the same role that
  LaplaceConvolution.v plays for the density.

  THE RESULT ([lcc_convolution_cdf], for [0 < b]):

      INT  f_b(u) * F_b(u + t)  du  =  G_b(t)

      G_b(t) = (1/4) * (2 - t/b) * exp(t/b)            for t <= 0
             = 1 - (1/4) * (2 + t/b) * exp(-t/b)       for t >= 0

  where [f_b] is the centred Laplace density ([lc_density]) and [F_b] its CDF
  ([laplace_cdf 0 b]).  Probabilistically this is [P[X - Y <= t]] for
  independent [X], [Y] ~ Laplace(0, b), i.e. the CDF whose density
  LaplaceConvolution.v computes.  The two agree at [t = 0], where both give
  [1/2] by symmetry.

  WHY A SEPARATE LEMMA.  LaplaceConvolution.v gives the DENSITY of the
  difference.  Getting an event probability out of it would need the
  fundamental theorem of calculus, which CPHL.v does not have -- [real_integral]
  comes with extensionality, additivity, scaling and five closed forms, and
  nothing links it to differentiation.  So the cumulative form has to be
  integrated directly, which is what this file does.

  THE PROOF.  Same shape as LaplaceConvolution.v: the integrand is piecewise
  exponential with breakpoints at [0] (from [|u|]) and [-t] (from the sign of
  [u + t]), so the line splits into three half-open regions on each of which
  the integrand is an exponential, a constant, or a difference of the two.
  The [1] inside [F_b] on the upper regions is what produces the constant
  terms, and hence the [1 -] in the answer.

  No new axioms.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
Require Import CPHL.
Require Import LaplaceConvolution.

Open Scope R_scope.

(** * The two branches of the Laplace CDF at location 0 *)

Lemma lcc_F_nonpos :
  forall b x : R, (x <= 0)%R -> laplace_cdf 0 b x = ((1 / 2) * exp (x / b))%R.
Proof.
  intros b x Hx.
  unfold laplace_cdf.
  destruct (Rle_dec x 0) as [H | H]; [| lra].
  replace (x - 0)%R with x by ring; reflexivity.
Qed.

Lemma lcc_F_pos :
  forall b x : R,
    (0 < x)%R -> laplace_cdf 0 b x = (1 - (1 / 2) * exp (- x / b))%R.
Proof.
  intros b x Hx.
  unfold laplace_cdf.
  destruct (Rle_dec x 0) as [H | H]; [lra |].
  replace (- (x - 0))%R with (- x)%R by ring; reflexivity.
Qed.

(** Both branches agree at [x = 0], so the nonneg version is uniform. *)
Lemma lcc_F_nonneg :
  forall b x : R,
    (0 < b)%R -> (0 <= x)%R ->
    laplace_cdf 0 b x = (1 - (1 / 2) * exp (- x / b))%R.
Proof.
  intros b x Hb Hx.
  assert (Hb2 : (b <> 0)%R) by lra.
  unfold laplace_cdf.
  destruct (Rle_dec x 0) as [H | H].
  - assert (Hx0 : x = 0%R) by lra.
    subst x.
    replace ((0 - 0) / b)%R with 0%R by (field; exact Hb2).
    replace (- 0 / b)%R with 0%R by (field; exact Hb2).
    rewrite exp_0; lra.
  - replace (- (x - 0))%R with (- x)%R by ring; reflexivity.
Qed.

(** * One more region integral: an exponential over a bounded window *)

Lemma lcc_between_exp :
  forall m M k C : R,
    (m <= M)%R ->
    k <> 0%R ->
    real_integral (fun u => real_indicator (m <= u < M)%R * (C * exp (k * u))) =
    (C * ((exp (k * M) - exp (k * m)) / k))%R.
Proof.
  intros m M k C Hm Hk.
  rewrite <- (real_integral_exp_between m M k Hm Hk).
  unfold real_integral_between.
  rewrite <- real_integral_scale.
  apply real_integral_extensional; intro u; ring.
Qed.

Lemma lcc_int_minus :
  forall f g : R -> R,
    real_integral (fun x => (f x - g x)%R) =
    (real_integral f - real_integral g)%R.
Proof.
  intros f g.
  transitivity (real_integral (fun x => (f x + (-1) * g x)%R)).
  - apply real_integral_extensional; intro x; ring.
  - rewrite real_integral_add, real_integral_scale; ring.
Qed.

(** Splitting a region integrand that is a difference. *)
Lemma lcc_region_minus :
  forall (P : R -> Prop) (A B : R -> R),
    real_integral (fun u => real_indicator (P u) * (A u - B u))%R =
    (real_integral (fun u => real_indicator (P u) * A u)
     - real_integral (fun u => real_indicator (P u) * B u))%R.
Proof.
  intros P A B.
  rewrite <- lcc_int_minus.
  apply real_integral_extensional; intro u; ring.
Qed.

(** * The answer *)

Definition lcc_G (b t : R) : R :=
  if Rle_dec t 0
  then ((1 / 4) * (2 - t / b) * exp (t / b))%R
  else (1 - (1 / 4) * (2 + t / b) * exp (- t / b))%R.

(** * The cumulative convolution *)

Theorem lcc_convolution_cdf :
  forall b t : R,
    (0 < b)%R ->
    real_integral (fun u => lc_density b u * laplace_cdf 0 b (u + t)) =
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
    rewrite (lc_split 0 (- t) _ Hmt).
    (* region u < 0 : |u| = -u, u + t < 0 *)
    rewrite (real_integral_extensional
               (fun u => real_indicator (u < 0)%R
                         * (lc_density b u * laplace_cdf 0 b (u + t)))
               (fun u => real_indicator (u < 0)%R
                         * (((1 / (4 * b)) * exp (t / b))
                            * exp ((2 / b) * u)))).
    2:{ intro u.
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
    (* region 0 <= u < -t : |u| = u, u + t <= 0 *)
    rewrite (real_integral_extensional
               (fun u => real_indicator (0 <= u < - t)%R
                         * (lc_density b u * laplace_cdf 0 b (u + t)))
               (fun u => real_indicator (0 <= u < - t)%R
                         * ((1 / (4 * b)) * exp (t / b)))).
    2:{ intro u.
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
    (* region -t <= u : |u| = u, u + t >= 0 *)
    rewrite (real_integral_extensional
               (fun u => real_indicator (- t <= u)%R
                         * (lc_density b u * laplace_cdf 0 b (u + t)))
               (fun u => real_indicator (- t <= u)%R
                         * (((1 / (2 * b)) * exp ((- (1 / b)) * u))
                            - ((1 / (4 * b)) * exp (- t / b))
                              * exp ((- (2 / b)) * u)))).
    2:{ intro u.
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
    rewrite (lc_below_exp 0 (2 / b) _ Hk).
    rewrite (lc_between_const 0 (- t) _ Hmt).
    rewrite lcc_region_minus.
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
    rewrite (lc_split (- t) 0 _ Hmt).
    (* region u < -t : |u| = -u, u + t < 0 *)
    rewrite (real_integral_extensional
               (fun u => real_indicator (u < - t)%R
                         * (lc_density b u * laplace_cdf 0 b (u + t)))
               (fun u => real_indicator (u < - t)%R
                         * (((1 / (4 * b)) * exp (t / b))
                            * exp ((2 / b) * u)))).
    2:{ intro u.
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
    (* region -t <= u < 0 : |u| = -u, u + t >= 0 *)
    rewrite (real_integral_extensional
               (fun u => real_indicator (- t <= u < 0)%R
                         * (lc_density b u * laplace_cdf 0 b (u + t)))
               (fun u => real_indicator (- t <= u < 0)%R
                         * (((1 / (2 * b)) * exp ((1 / b) * u))
                            - (1 / (4 * b)) * exp (- t / b)))).
    2:{ intro u.
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
    (* region 0 <= u : |u| = u, u + t > 0 *)
    rewrite (real_integral_extensional
               (fun u => real_indicator (0 <= u)%R
                         * (lc_density b u * laplace_cdf 0 b (u + t)))
               (fun u => real_indicator (0 <= u)%R
                         * (((1 / (2 * b)) * exp ((- (1 / b)) * u))
                            - ((1 / (4 * b)) * exp (- t / b))
                              * exp ((- (2 / b)) * u)))).
    2:{ intro u.
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
    rewrite (lc_below_exp (- t) (2 / b) _ Hk).
    rewrite lcc_region_minus.
    rewrite (lcc_between_exp (- t) 0 (1 / b) _ Hmt) by lra.
    rewrite (lc_between_const (- t) 0 _ Hmt).
    rewrite lcc_region_minus.
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
