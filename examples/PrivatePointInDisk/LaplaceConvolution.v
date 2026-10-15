(**
  LaplaceConvolution.v -- analytic support, no program and no triple.

  [lc_convolution] (for 0 < b), with [f_b] the centred Laplace density
  [lc_density]:

      INT  f_b(u) * f_b(z - u)  du  =  (1/(4b)) * (1 + |z|/b) * exp(-|z|/b)

  i.e. the density of the difference of two independent Laplace(0, b)
  variables; [lc_difference_not_laplace] shows it is not a Laplace density.
  Axiom-free: the exponential-region integrals come from
  CPHLFacts.ExponentialIntegrals and the constant-region integral from
  CPHLFacts.RealIntegrationFacts.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Require Import MeasureIntegration CPHL.
Require Import CPHLFacts.CalculationFacts.
Require Import CPHLFacts.RealIntegrationFacts.
Require Import CPHLFacts.ExponentialIntegrals.

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

(** Splitting an integral over the three regions, given the integrand's
    form on each region and integrability of those forms. *)
Lemma lc_split3 :
  forall (m M : R) (g A B C : R -> R),
    (m <= M)%R ->
    (forall u, real_indicator (u < m)%R * g u = real_indicator (u < m)%R * A u) ->
    (forall u, real_indicator (m <= u < M)%R * g u
               = real_indicator (m <= u < M)%R * B u) ->
    (forall u, real_indicator (M <= u)%R * g u = real_indicator (M <= u)%R * C u) ->
    real_integrable (fun u => real_indicator (u < m)%R * A u) ->
    real_integrable (fun u => real_indicator (m <= u < M)%R * B u) ->
    real_integrable (fun u => real_indicator (M <= u)%R * C u) ->
    real_integral g =
    (real_integral (fun u => real_indicator (u < m)%R * A u)
     + real_integral (fun u => real_indicator (m <= u < M)%R * B u)
     + real_integral (fun u => real_indicator (M <= u)%R * C u))%R.
Proof.
  intros m M g A B C Hm HA HB HC IA IB IC.
  rewrite <- real_integral_add, <- real_integral_add.
  - apply real_integral_extensional; intro u.
    rewrite <- HA, <- HB, <- HC.
    rewrite <- (Rmult_1_l (g u)) at 1.
    rewrite <- (lc_indicator_partition m M u Hm).
    ring.
  all: first [ exact IA | exact IB | exact IC
             | exact (@ConcreteMeasure.integrable_add _ RealIntegration.Space
                 RealIntegration.lebesgue _ _ IA IB) ].
Qed.

(** * The three region integrals *)

Lemma lc_below_exp :
  forall m k C : R,
    (0 < k)%R ->
    real_integral (fun u => real_indicator (u < m)%R * (C * exp (k * u))) =
    (C * (exp (k * m) / k))%R.
Proof.
  intros m k C Hk.
  rewrite <- (real_integral_exp_below_proved m k Hk).
  unfold real_integral_below.
  rewrite <- real_integral_scale by (apply real_integrable_exp_below; exact Hk).
  apply real_integral_extensional; intro u; ring.
Qed.

Lemma lc_above_exp :
  forall M k C : R,
    (k < 0)%R ->
    real_integral (fun u => real_indicator (M <= u)%R * (C * exp (k * u))) =
    (C * (- exp (k * M) / k))%R.
Proof.
  intros M k C Hk.
  rewrite <- (real_integral_exp_above_proved M k Hk).
  unfold real_integral_above.
  rewrite <- real_integral_scale by (apply real_integrable_exp_above; exact Hk).
  apply real_integral_extensional; intro u; ring.
Qed.

Lemma lc_between_const :
  forall m M C : R,
    (m <= M)%R ->
    real_integral (fun u => real_indicator (m <= u < M)%R * C) =
    (C * (M - m))%R.
Proof.
  intros m M C Hm.
  transitivity (real_integral (fun u => C * (real_indicator (m <= u < M)%R * 1)))%R.
  - apply real_integral_extensional; intro u; ring.
  - rewrite real_integral_scale by apply real_integrable_between_one.
    assert (H : real_integral (fun u => real_indicator (m <= u < M)%R * 1)%R
                = (M - m)%R) by exact (real_integral_between_one m M Hm).
    rewrite H; reflexivity.
Qed.

(** Integrability of the region forms used below. *)
Lemma lc_integrable_minus :
  forall (A : R -> Prop) (f g : R -> R),
    real_integrable (fun x => real_indicator (A x) * f x) ->
    real_integrable (fun x => real_indicator (A x) * g x) ->
    real_integrable (fun x => real_indicator (A x) * (f x - g x))%R.
Proof.
  intros A f g Hf Hg.
  apply real_integrable_ext with
    (f := fun x => (real_indicator (A x) * f x
                    + (-1) * (real_indicator (A x) * g x))%R).
  - intro x; ring.
  - exact (@ConcreteMeasure.integrable_add _ RealIntegration.Space
      RealIntegration.lebesgue _ _ Hf
      (@ConcreteMeasure.integrable_scale _ RealIntegration.Space
         RealIntegration.lebesgue (-1) _ Hg)).
Qed.

Ltac lc_integrable :=
  first
    [ apply real_integrable_between_constant
    | apply lc_integrable_minus; lc_integrable
    | apply real_integrable_mask_scale;
      first [ apply real_integrable_exp_between
            | apply real_integrable_exp_below; assumption
            | apply real_integrable_exp_above; assumption ] ].

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
    rewrite (lc_split3 0 z _
               (fun u => (((1 / (4 * b * b)) * exp (- z / b))
                            * exp ((2 / b) * u)))
               (fun u => ((1 / (4 * b * b)) * exp (- z / b)))
               (fun u => (((1 / (4 * b * b)) * exp (z / b))
                            * exp ((- (2 / b)) * u))) Hz).
    2:{ intro u; cbv beta.
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
    2:{ intro u; cbv beta.
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
    2:{ intro u; cbv beta.
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
    2-4: lc_integrable.
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
    rewrite (lc_split3 z 0 _
               (fun u => (((1 / (4 * b * b)) * exp (- z / b))
                            * exp ((2 / b) * u)))
               (fun u => ((1 / (4 * b * b)) * exp (z / b)))
               (fun u => (((1 / (4 * b * b)) * exp (z / b))
                            * exp ((- (2 / b)) * u))) Hzle).
    2:{ intro u; cbv beta.
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
    2:{ intro u; cbv beta.
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
    2:{ intro u; cbv beta.
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
    2-4: lc_integrable.
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
