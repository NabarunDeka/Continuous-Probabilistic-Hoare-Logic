(**
  LaplaceConvolution.v -- the law of a SUM (equivalently, a difference) of
  two independent Laplace variables.

  NO TRIPLE.  This file contains no command and no assertion; it is a purely
  analytic lemma about [real_integral], in the same role that
  UniformConstructions/UniformAxiomsAdditional.v plays for the uniform
  examples.

  THE RESULT ([lc_convolution], for [0 < b]):

      INT  f_b(u) * f_b(z - u)  du  =  (1/(4b)) * (1 + |z|/b) * exp(-|z|/b)

  where [f_b] is the centred Laplace density [lc_density].  Since the
  Laplace law is symmetric, [-Y] is Laplace whenever [Y] is, so this is
  simultaneously the density of [X + Y] and of [X - Y] for independent
  [X], [Y] ~ Laplace(0, b).

  WHY IT IS WORTH STATING: THE DIFFERENCE OF TWO LAPLACES IS NOT LAPLACE.

  A centred Laplace density is [(1/(2c)) exp(-|z|/c)] -- log-linear in |z|.
  The density above carries an extra [(1 + |z|/b)] factor, so its log is not
  linear and no choice of [c] matches it.  Equivalently, the characteristic
  function is [1/(1 + b^2 t^2)^2] rather than [1/(1 + b^2 t^2)].  It agrees
  with Laplace(0, 2b) at [z = 0] and shares the tail rate of Laplace(0, b),
  which is presumably why the mistake is tempting; it equals neither.

  This matters for PointInDiskInPlace.v / PointInDiskAdditive.v.  Perturbing
  the point and the centre SEPARATELY and then testing membership leaves the
  two differences [px' - cx'] and [py' - cy'] distributed as above -- NOT as
  Laplace -- so any reduction of that variant which assumes otherwise is
  wrong.  See flags/FLAGS.md F14.

  It does not, on its own, unblock that variant: the obstruction there is
  the DISK, whose sections have square-root endpoints, and that survives any
  reduction of the noise count.  What this lemma does enable is the
  one-dimensional version, where the region is an interval and no square
  root appears.

  THE PROOF.  Both densities are exponentials of absolute values, so the
  product is [exp] of [-(|u| + |z-u|)/b], and that exponent is piecewise
  linear with breakpoints at [0] and [z].  Splitting the line into the three
  half-open regions [u < m], [m <= u < M], [M <= u] (with [m], [M] the
  smaller and larger of [0] and [z]) makes each piece a bare exponential or
  a constant, which is exactly what CPHL.v's [real_integral_exp_below],
  [real_integral_exp_above] and [real_integral_between_constant] evaluate.
  The two ends contribute [b/2] each and the middle contributes [|z|], which
  is where the [(b + |z|)] factor comes from.

  No new axioms: the three exponential-region laws and the linearity of
  [real_integral], all already in CPHL.v.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
Require Import CPHL.

Open Scope R_scope.

(** * The centred Laplace density

    Same convention as [CPHL.distribution_density] at [Laplace 0 b]. *)

Definition lc_density (b x : R) : R := ((1 / (2 * b)) * exp (- Rabs x / b))%R.

Lemma lc_density_is_laplace :
  forall (b x : R) (v : state),
    lc_density b x = distribution_density (Laplace (TConst 0) (TConst b)) v x.
Proof.
  intros b x v.
  cbn [distribution_density term_eval].
  unfold lc_density.
  replace (x - 0)%R with x by ring.
  reflexivity.
Qed.

(** * Splitting the line into three half-open regions *)

Lemma lc_indicator_partition :
  forall m M u : R,
    (m <= M)%R ->
    (real_indicator (u < m)%R + real_indicator (m <= u < M)%R
       + real_indicator (M <= u)%R)%R = 1%R.
Proof.
  intros m M u Hm.
  destruct (Rlt_dec u m) as [H1 | H1].
  - rewrite (real_indicator_true (u < m)%R H1).
    rewrite (real_indicator_false (m <= u < M)%R) by (intros [Ha _]; lra).
    rewrite (real_indicator_false (M <= u)%R) by lra.
    ring.
  - destruct (Rlt_dec u M) as [H2 | H2].
    + rewrite (real_indicator_false (u < m)%R) by lra.
      rewrite (real_indicator_true (m <= u < M)%R (conj (Rnot_lt_le _ _ H1) H2)).
      rewrite (real_indicator_false (M <= u)%R) by lra.
      ring.
    + rewrite (real_indicator_false (u < m)%R) by lra.
      rewrite (real_indicator_false (m <= u < M)%R) by (intros [_ Hb]; lra).
      rewrite (real_indicator_true (M <= u)%R) by lra.
      ring.
Qed.

Lemma lc_split :
  forall (m M : R) (g : R -> R),
    (m <= M)%R ->
    real_integral g =
    (real_integral (fun u => real_indicator (u < m)%R * g u)
     + real_integral (fun u => real_indicator (m <= u < M)%R * g u)
     + real_integral (fun u => real_indicator (M <= u)%R * g u))%R.
Proof.
  intros m M g Hm.
  rewrite <- real_integral_add, <- real_integral_add.
  apply real_integral_extensional; intro u.
  rewrite <- (Rmult_1_l (g u)) at 1.
  rewrite <- (lc_indicator_partition m M u Hm).
  ring.
Qed.

(** * The three region integrals *)

Lemma lc_below_exp :
  forall m k C : R,
    (0 < k)%R ->
    real_integral (fun u => real_indicator (u < m)%R * (C * exp (k * u))) =
    (C * (exp (k * m) / k))%R.
Proof.
  intros m k C Hk.
  rewrite <- (real_integral_exp_below m k Hk).
  unfold real_integral_below.
  rewrite <- real_integral_scale.
  apply real_integral_extensional; intro u; ring.
Qed.

Lemma lc_above_exp :
  forall M k C : R,
    (k < 0)%R ->
    real_integral (fun u => real_indicator (M <= u)%R * (C * exp (k * u))) =
    (C * (- exp (k * M) / k))%R.
Proof.
  intros M k C Hk.
  rewrite <- (real_integral_exp_above M k Hk).
  unfold real_integral_above.
  rewrite <- real_integral_scale.
  apply real_integral_extensional; intro u; ring.
Qed.

Lemma lc_between_const :
  forall m M C : R,
    (m <= M)%R ->
    real_integral (fun u => real_indicator (m <= u < M)%R * C) =
    (C * (M - m))%R.
Proof.
  intros m M C Hm.
  rewrite <- (real_integral_between_constant m M C Hm).
  unfold real_integral_between.
  apply real_integral_extensional; intro u; ring.
Qed.

(** * The product of the two densities is a single exponential *)

Lemma lc_pair :
  forall b p q : R,
    (0 < b)%R ->
    ((1 / (2 * b)) * exp (- p / b) * ((1 / (2 * b)) * exp (- q / b)))%R =
    ((1 / (4 * b * b)) * exp (- (p + q) / b))%R.
Proof.
  intros b p q Hb.
  assert (Hb2 : (b <> 0)%R) by lra.
  replace (- (p + q) / b)%R with (- p / b + - q / b)%R by (field; exact Hb2).
  rewrite exp_plus; field; exact Hb2.
Qed.

(** * The convolution *)

Theorem lc_convolution :
  forall b z : R,
    (0 < b)%R ->
    real_integral (fun u => lc_density b u * lc_density b (z - u)) =
    ((1 / (4 * b)) * (1 + Rabs z / b) * exp (- Rabs z / b))%R.
Proof.
  intros b z Hb.
  assert (Hb2 : (b <> 0)%R) by lra.
  assert (Hk : (0 < 2 / b)%R)
    by (unfold Rdiv; apply Rmult_lt_0_compat;
        [lra | apply Rinv_0_lt_compat; exact Hb]).
  assert (Hkn : (- (2 / b) < 0)%R) by lra.
  destruct (Rle_dec 0 z) as [Hz | Hz].
  - (* z >= 0 : breakpoints 0 then z *)
    rewrite (lc_split 0 z _ Hz).
    rewrite (real_integral_extensional
               (fun u => real_indicator (u < 0)%R
                         * (lc_density b u * lc_density b (z - u)))
               (fun u => real_indicator (u < 0)%R
                         * (((1 / (4 * b * b)) * exp (- z / b))
                            * exp ((2 / b) * u)))).
    2:{ intro u.
        destruct (Rlt_dec u 0) as [Hu | Hu].
        - rewrite (real_indicator_true (u < 0)%R Hu).
          unfold lc_density.
          rewrite (Rabs_left u Hu).
          rewrite (Rabs_pos_eq (z - u)) by lra.
          rewrite (lc_pair b (- u) (z - u) Hb).
          replace (- (- u + (z - u)) / b)%R with (- z / b + 2 / b * u)%R
            by (field; exact Hb2).
          rewrite exp_plus; ring.
        - rewrite (real_indicator_false (u < 0)%R) by lra; ring. }
    rewrite (real_integral_extensional
               (fun u => real_indicator (0 <= u < z)%R
                         * (lc_density b u * lc_density b (z - u)))
               (fun u => real_indicator (0 <= u < z)%R
                         * ((1 / (4 * b * b)) * exp (- z / b)))).
    2:{ intro u.
        destruct (Rle_dec 0 u) as [Hu1 | Hu1];
          [destruct (Rlt_dec u z) as [Hu2 | Hu2] |].
        - rewrite (real_indicator_true (0 <= u < z)%R (conj Hu1 Hu2)).
          unfold lc_density.
          rewrite (Rabs_pos_eq u) by lra.
          rewrite (Rabs_pos_eq (z - u)) by lra.
          rewrite (lc_pair b u (z - u) Hb).
          replace (- (u + (z - u)) / b)%R with (- z / b)%R
            by (field; exact Hb2).
          ring.
        - rewrite (real_indicator_false (0 <= u < z)%R)
            by (intros [_ Hc]; lra); ring.
        - rewrite (real_indicator_false (0 <= u < z)%R)
            by (intros [Hc _]; lra); ring. }
    rewrite (real_integral_extensional
               (fun u => real_indicator (z <= u)%R
                         * (lc_density b u * lc_density b (z - u)))
               (fun u => real_indicator (z <= u)%R
                         * (((1 / (4 * b * b)) * exp (z / b))
                            * exp ((- (2 / b)) * u)))).
    2:{ intro u.
        destruct (Rle_dec z u) as [Hu | Hu].
        - rewrite (real_indicator_true (z <= u)%R Hu).
          unfold lc_density.
          rewrite (Rabs_pos_eq u) by lra.
          rewrite (Rabs_left1 (z - u)) by lra.
          rewrite (lc_pair b u (- (z - u)) Hb).
          replace (- (u + - (z - u)) / b)%R with (z / b + - (2 / b) * u)%R
            by (field; exact Hb2).
          rewrite exp_plus; ring.
        - rewrite (real_indicator_false (z <= u)%R) by lra; ring. }
    rewrite (lc_below_exp 0 (2 / b) _ Hk).
    rewrite (lc_between_const 0 z _ Hz).
    rewrite (lc_above_exp z (- (2 / b)) _ Hkn).
    rewrite (Rabs_pos_eq z Hz).
    replace (2 / b * 0)%R with 0%R by ring.
    rewrite exp_0.
    set (E := exp (z / b)).
    assert (HE : (0 < E)%R) by (unfold E; apply exp_pos).
    assert (HE0 : (E <> 0)%R) by (apply Rgt_not_eq; exact HE).
    assert (H1 : exp (- z / b) = (/ E)%R).
    { unfold E; rewrite <- exp_Ropp; f_equal; field; exact Hb2. }
    assert (H2 : exp (- (2 / b) * z) = (/ E * / E)%R).
    { replace (- (2 / b) * z)%R with (- (z / b) + - (z / b))%R
        by (field; exact Hb2).
      rewrite exp_plus; unfold E; rewrite exp_Ropp; reflexivity. }
    rewrite H1, H2.
    field; repeat split; try lra; exact HE0.
  - (* z < 0 : breakpoints z then 0 *)
    assert (Hzlt : (z < 0)%R) by lra.
    assert (Hzle : (z <= 0)%R) by lra.
    rewrite (lc_split z 0 _ Hzle).
    rewrite (real_integral_extensional
               (fun u => real_indicator (u < z)%R
                         * (lc_density b u * lc_density b (z - u)))
               (fun u => real_indicator (u < z)%R
                         * (((1 / (4 * b * b)) * exp (- z / b))
                            * exp ((2 / b) * u)))).
    2:{ intro u.
        destruct (Rlt_dec u z) as [Hu | Hu].
        - rewrite (real_indicator_true (u < z)%R Hu).
          unfold lc_density.
          rewrite (Rabs_left u) by lra.
          rewrite (Rabs_pos_eq (z - u)) by lra.
          rewrite (lc_pair b (- u) (z - u) Hb).
          replace (- (- u + (z - u)) / b)%R with (- z / b + 2 / b * u)%R
            by (field; exact Hb2).
          rewrite exp_plus; ring.
        - rewrite (real_indicator_false (u < z)%R) by lra; ring. }
    rewrite (real_integral_extensional
               (fun u => real_indicator (z <= u < 0)%R
                         * (lc_density b u * lc_density b (z - u)))
               (fun u => real_indicator (z <= u < 0)%R
                         * ((1 / (4 * b * b)) * exp (z / b)))).
    2:{ intro u.
        destruct (Rle_dec z u) as [Hu1 | Hu1];
          [destruct (Rlt_dec u 0) as [Hu2 | Hu2] |].
        - rewrite (real_indicator_true (z <= u < 0)%R (conj Hu1 Hu2)).
          unfold lc_density.
          rewrite (Rabs_left u Hu2).
          rewrite (Rabs_left1 (z - u)) by lra.
          rewrite (lc_pair b (- u) (- (z - u)) Hb).
          replace (- (- u + - (z - u)) / b)%R with (z / b)%R
            by (field; exact Hb2).
          ring.
        - rewrite (real_indicator_false (z <= u < 0)%R)
            by (intros [_ Hc]; lra); ring.
        - rewrite (real_indicator_false (z <= u < 0)%R)
            by (intros [Hc _]; lra); ring. }
    rewrite (real_integral_extensional
               (fun u => real_indicator (0 <= u)%R
                         * (lc_density b u * lc_density b (z - u)))
               (fun u => real_indicator (0 <= u)%R
                         * (((1 / (4 * b * b)) * exp (z / b))
                            * exp ((- (2 / b)) * u)))).
    2:{ intro u.
        destruct (Rle_dec 0 u) as [Hu | Hu].
        - rewrite (real_indicator_true (0 <= u)%R Hu).
          unfold lc_density.
          rewrite (Rabs_pos_eq u Hu).
          rewrite (Rabs_left1 (z - u)) by lra.
          rewrite (lc_pair b u (- (z - u)) Hb).
          replace (- (u + - (z - u)) / b)%R with (z / b + - (2 / b) * u)%R
            by (field; exact Hb2).
          rewrite exp_plus; ring.
        - rewrite (real_indicator_false (0 <= u)%R) by lra; ring. }
    rewrite (lc_below_exp z (2 / b) _ Hk).
    rewrite (lc_between_const z 0 _ Hzle).
    rewrite (lc_above_exp 0 (- (2 / b)) _ Hkn).
    rewrite (Rabs_left z Hzlt).
    replace (- - z / b)%R with (z / b)%R by (field; exact Hb2).
    replace (- (2 / b) * 0)%R with 0%R by ring.
    rewrite exp_0.
    set (E := exp (z / b)).
    assert (HE : (0 < E)%R) by (unfold E; apply exp_pos).
    assert (HE0 : (E <> 0)%R) by (apply Rgt_not_eq; exact HE).
    assert (H1 : exp (- z / b) = (/ E)%R).
    { unfold E; rewrite <- exp_Ropp; f_equal; field; exact Hb2. }
    assert (H2 : exp (2 / b * z) = (E * E)%R).
    { replace (2 / b * z)%R with (z / b + z / b)%R by (field; exact Hb2).
      rewrite exp_plus; reflexivity. }
    rewrite H1, H2.
    field; repeat split; try lra; exact HE0.
Qed.

(** * The difference of two Laplaces is NOT Laplace

    Not merely "has a different scale": no centred Laplace density whatsoever
    agrees with the convolution.  The proof is purely algebraic -- it needs
    no numeric bound on [exp], only the functional equation [exp_plus] and
    positivity.

    Evaluating at [0] forces the scale to be [2b].  Evaluating at [b] then
    gives [2 exp(-1) = exp(-1/2)], whose square says [exp(-1) = 1/4], and
    evaluating at [2b] gives [3 exp(-2) = exp(-1)], i.e. [3/16 = 1/4]. *)

Theorem lc_difference_not_laplace :
  forall b c : R,
    (0 < b)%R ->
    (0 < c)%R ->
    ~ (forall z : R,
         real_integral (fun u => lc_density b u * lc_density b (z - u)) =
         lc_density c z).
Proof.
  intros b c Hb Hc H.
  assert (Hb2 : (b <> 0)%R) by lra.
  assert (Hc2 : (c <> 0)%R) by lra.
  (* value at 0 pins the scale to 2b *)
  assert (H0 := H 0%R).
  rewrite (lc_convolution b 0 Hb) in H0.
  unfold lc_density in H0.
  rewrite Rabs_R0 in H0.
  replace (- 0 / b)%R with 0%R in H0 by (field; exact Hb2).
  replace (- 0 / c)%R with 0%R in H0 by (field; exact Hc2).
  rewrite exp_0 in H0.
  replace ((1 / (4 * b)) * (1 + 0 / b) * 1)%R with (1 / (4 * b))%R in H0
    by (field; exact Hb2).
  replace ((1 / (2 * c)) * 1)%R with (1 / (2 * c))%R in H0
    by (field; exact Hc2).
  assert (Hcb : c = (2 * b)%R).
  { assert (Hx : ((1 / (4 * b)) * (4 * b * (2 * c))
                  = (1 / (2 * c)) * (4 * b * (2 * c)))%R)
      by (rewrite H0; reflexivity).
    replace ((1 / (4 * b)) * (4 * b * (2 * c)))%R with (2 * c)%R in Hx
      by (field; exact Hb2).
    replace ((1 / (2 * c)) * (4 * b * (2 * c)))%R with (4 * b)%R in Hx
      by (field; exact Hc2).
    lra. }
  (* value at b *)
  assert (H1 := H b).
  rewrite (lc_convolution b b Hb) in H1.
  unfold lc_density in H1.
  rewrite (Rabs_pos_eq b) in H1 by lra.
  rewrite Hcb in H1.
  replace (- b / b)%R with (-1)%R in H1 by (field; exact Hb2).
  replace (- b / (2 * b))%R with (- (1 / 2))%R in H1 by (field; exact Hb2).
  replace (1 + b / b)%R with 2%R in H1 by (field; exact Hb2).
  assert (Ha : (2 * exp (-1) = exp (- (1 / 2)))%R).
  { assert (Hx : ((1 / (4 * b)) * 2 * exp (-1) * (4 * b)
                  = (1 / (2 * (2 * b))) * exp (- (1 / 2)) * (4 * b))%R)
      by (rewrite H1; reflexivity).
    replace ((1 / (4 * b)) * 2 * exp (-1) * (4 * b))%R
      with (2 * exp (-1))%R in Hx by (field; exact Hb2).
    replace ((1 / (2 * (2 * b))) * exp (- (1 / 2)) * (4 * b))%R
      with (exp (- (1 / 2)))%R in Hx by (field; exact Hb2).
    exact Hx. }
  (* value at 2b *)
  assert (H2 := H (2 * b)%R).
  rewrite (lc_convolution b (2 * b) Hb) in H2.
  unfold lc_density in H2.
  rewrite (Rabs_pos_eq (2 * b)) in H2 by lra.
  rewrite Hcb in H2.
  replace (- (2 * b) / b)%R with (-2)%R in H2 by (field; exact Hb2).
  replace (- (2 * b) / (2 * b))%R with (-1)%R in H2 by (field; exact Hb2).
  replace (1 + 2 * b / b)%R with 3%R in H2 by (field; exact Hb2).
  assert (Hbb : (3 * exp (-2) = exp (-1))%R).
  { assert (Hx : ((1 / (4 * b)) * 3 * exp (-2) * (4 * b)
                  = (1 / (2 * (2 * b))) * exp (-1) * (4 * b))%R)
      by (rewrite H2; reflexivity).
    replace ((1 / (4 * b)) * 3 * exp (-2) * (4 * b))%R
      with (3 * exp (-2))%R in Hx by (field; exact Hb2).
    replace ((1 / (2 * (2 * b))) * exp (-1) * (4 * b))%R
      with (exp (-1))%R in Hx by (field; exact Hb2).
    exact Hx. }
  (* the two functional equations are incompatible *)
  assert (Hsq : (exp (- (1 / 2)) * exp (- (1 / 2)) = exp (-1))%R).
  { rewrite <- exp_plus; f_equal; field. }
  assert (Hsq2 : (exp (-1) * exp (-1) = exp (-2))%R).
  { rewrite <- exp_plus; f_equal; field. }
  assert (Hp : (0 < exp (-1))%R) by apply exp_pos.
  rewrite <- Ha in Hsq.
  assert (HE : exp (-1) = (1 / 4)%R) by nra.
  rewrite HE in Hsq2.
  rewrite <- Hsq2 in Hbb.
  lra.
Qed.
