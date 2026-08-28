(**
  The two-query Sparse Vector Technique instance from the motivating example
  of "Deciding Differential Privacy for Programs with Finite Inputs and
  Outputs".

  This file is a self-contained, notation-oriented presentation of the full
  development.  It depends on [CPHL] alone: every analytical and Hoare proof
  is reproduced locally, while the syntax-facing definitions use [<{ ... }>],
  [[[ ... ]]], and [{{ ... }} ... {{ ... }}] wherever those interfaces apply.

  The paper writes [Lap(rate, location)], whereas [CPHL.Laplace] stores
  [(location, scale)].  Consequently the rates [epsilon/2] and [epsilon/4]
  below become the scales [2/epsilon] and [4/epsilon].
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Psatz.
From Stdlib Require Import Field.
From Stdlib Require Import Ring.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import ClassicalDescription.

Require Import CPHL.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** Program variables. *)
Definition q1 : RealProgramVar := real_program_var "q1".
Definition q2 : RealProgramVar := real_program_var "q2".
Definition threshold : RealProgramVar := real_program_var "threshold".
Definition noisy1 : RealProgramVar := real_program_var "noisy1".
Definition noisy2 : RealProgramVar := real_program_var "noisy2".

Definition above1 : BoolProgramVar := bool_program_var "above1".
Definition above2 : BoolProgramVar := bool_program_var "above2".
Definition out1 : BoolProgramVar := bool_program_var "out1".
Definition out2 : BoolProgramVar := bool_program_var "out2".

(** Rigid variables used only inside the derived conditional proof. *)
Definition y_then : ProbLogicVar := prob_logic_var "y_then".
Definition y_else : ProbLogicVar := prob_logic_var "y_else".

Definition threshold_distribution (epsilon : R) : Distribution :=
  <{ laplace ( 0, $((2 / epsilon)%R) ) }>.

Definition query_distribution
  (epsilon : R) (query : RealProgramVar) : Distribution :=
  <{ laplace ( query, $((4 / epsilon)%R) ) }>.

Definition first_comparison : CFormula :=
  <{ threshold <= noisy1 }>.

Definition second_comparison : CFormula :=
  <{ threshold <= noisy2 }>.

(** The second unfolded iteration is executed only after the first answer was
    [bot]. *)
Definition second_iteration (epsilon : R) : Cmd :=
  <{
    noisy2 sample $(query_distribution epsilon q2);
    above2 b= $(second_comparison);
    if above2 then out2 b= true else skip end
  }>.

(** The generic [N = 2], [c = 1] SVT command.  The output initialization is
    explicit, and the true branch of the first comparison implements the
    early exit. *)
Definition two_queries (epsilon : R) : Cmd :=
  <{
    out1 b= false;
    out2 b= false;
    threshold sample $(threshold_distribution epsilon);
    noisy1 sample $(query_distribution epsilon q1);
    above1 b= $(first_comparison);
    if above1 then out1 b= true
    else $(second_iteration epsilon)
    end
  }>.

(** A concrete run on the input vector [[0, 1]]. *)
Definition run_01 (epsilon : R) : Cmd :=
  <{ q1 := 0; q2 := 1; $(two_queries epsilon) }>.

Definition bot_top : CFormula :=
  <{ ~ out1 /\ out2 }>.

Definition path_event : CFormula :=
  <{ noisy1 < threshold /\ threshold <= noisy2 }>.

Definition path_integral (epsilon : R) : PConstruct :=
  [[
    integral threshold ~ $(threshold_distribution epsilon),
    integral noisy1 ~ $(query_distribution epsilon q1),
    integral noisy2 ~ $(query_distribution epsilon q2),
    indicator[$(path_event)]
  ]].

Definition path_integral_01 (epsilon : R) : PConstruct :=
  [[
    integral threshold ~ $(threshold_distribution epsilon),
    integral noisy1 ~ laplace ( 0, $((4 / epsilon)%R) ),
    integral noisy2 ~ laplace ( 1, $((4 / epsilon)%R) ),
    indicator[$(path_event)]
  ]].

Definition bot_top_probability (r : R) : PFormula :=
  [[ Pr[$(bot_top)] = $(r) ]].

Definition normalized : PFormula :=
  [[ Pr[true] = 1 ]].

(** The paper prints a plus sign before the [21 exp(epsilon/2)] term.  That
    expression exceeds one for small positive epsilon.  Direct integration
    gives the corrected minus sign below. *)
Definition closed_form_probability (epsilon : R) : R :=
  (24 * exp (3 * epsilon / 4) - 1 + 8 * exp (epsilon / 4) -
    21 * exp (epsilon / 2)) /
  (48 * exp (3 * epsilon / 4)).

Lemma threshold_scale_positive :
  forall epsilon : R, (0 < epsilon)%R -> (0 < 2 / epsilon)%R.
Proof.
  intros epsilon Hepsilon.
  unfold Rdiv.
  apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; exact Hepsilon].
Qed.

Lemma query_scale_positive :
  forall epsilon : R, (0 < epsilon)%R -> (0 < 4 / epsilon)%R.
Proof.
  intros epsilon Hepsilon.
  unfold Rdiv.
  apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; exact Hepsilon].
Qed.

(** Raw analytical presentation of the nested probability construct. *)
Definition laplace_density_R (location scale z : R) : R :=
  (1 / (2 * scale)) * exp (- Rabs (z - location) / scale).

Definition nested_integral (epsilon : R) : R :=
  real_integral
    (fun threshold =>
      laplace_density_R 0 (2 / epsilon) threshold *
      real_integral
        (fun noisy1 =>
          laplace_density_R 0 (4 / epsilon) noisy1 *
          real_integral
            (fun noisy2 =>
              laplace_density_R 1 (4 / epsilon) noisy2 *
              real_indicator
                (noisy1 < threshold /\ threshold <= noisy2)%R))).

Definition threshold_integrand (epsilon threshold : R) : R :=
  laplace_density_R 0 (2 / epsilon) threshold *
  laplace_cdf 0 (4 / epsilon) threshold *
  (1 - laplace_cdf 1 (4 / epsilon) threshold).

Lemma nested_integral_reduce :
  forall epsilon : R,
    (0 < epsilon)%R ->
    nested_integral epsilon =
      real_integral (threshold_integrand epsilon).
Proof.
  intros epsilon Hepsilon.
  unfold nested_integral, threshold_integrand.
  apply real_integral_extensional.
  intro threshold.
  assert (Hinner :
    forall noisy1 : R,
      real_integral
        (fun noisy2 =>
          laplace_density_R 1 (4 / epsilon) noisy2 *
          real_indicator
            (noisy1 < threshold /\ threshold <= noisy2)%R) =
      (real_indicator (noisy1 < threshold)%R *
        (1 - laplace_cdf 1 (4 / epsilon) threshold))%R).
  {
    intro noisy1.
    destruct (Rlt_dec noisy1 threshold) as [Hlt | Hnlt].
    - rewrite (real_indicator_true _ Hlt).
      transitivity
        (real_integral
          (fun noisy2 =>
            laplace_density_R 1 (4 / epsilon) noisy2 *
            real_indicator (threshold <= noisy2)%R)).
      + apply real_integral_extensional.
        intro noisy2.
        destruct (Rle_dec threshold noisy2) as [Hle | Hnle].
        * rewrite (real_indicator_true _ (conj Hlt Hle)).
          rewrite (real_indicator_true _ Hle).
          reflexivity.
        * rewrite (real_indicator_false
            (noisy1 < threshold /\ threshold <= noisy2)%R) by tauto.
          rewrite (real_indicator_false (threshold <= noisy2)%R) by exact Hnle.
          ring.
      + unfold laplace_density_R.
        rewrite (laplace_integral_survival 1 (4 / epsilon) threshold
          (query_scale_positive epsilon Hepsilon)).
        ring.
    - rewrite (real_indicator_false (noisy1 < threshold)%R) by exact Hnlt.
      transitivity (real_integral (fun _ : R => 0%R)).
      + apply real_integral_extensional.
        intro noisy2.
        rewrite (real_indicator_false
          (noisy1 < threshold /\ threshold <= noisy2)%R) by tauto.
        ring.
      + rewrite real_integral_zero; ring.
  }
  assert (Hnoisy1 :
    real_integral
      (fun noisy1 =>
        laplace_density_R 0 (4 / epsilon) noisy1 *
        real_integral
          (fun noisy2 =>
            laplace_density_R 1 (4 / epsilon) noisy2 *
            real_indicator
              (noisy1 < threshold /\ threshold <= noisy2)%R)) =
    (laplace_cdf 0 (4 / epsilon) threshold *
      (1 - laplace_cdf 1 (4 / epsilon) threshold))%R).
  {
    transitivity
      (real_integral
        (fun noisy1 =>
          laplace_density_R 0 (4 / epsilon) noisy1 *
          (real_indicator (noisy1 < threshold)%R *
            (1 - laplace_cdf 1 (4 / epsilon) threshold)))).
    - apply real_integral_extensional.
      intro noisy1.
      rewrite Hinner.
      reflexivity.
    - transitivity
        ((real_integral
          (fun noisy1 =>
            laplace_density_R 0 (4 / epsilon) noisy1 *
            real_indicator (noisy1 < threshold)%R)) *
          (1 - laplace_cdf 1 (4 / epsilon) threshold))%R.
      + rewrite <- real_integral_scale_right.
        apply real_integral_extensional.
        intro noisy1.
        ring.
      + unfold laplace_density_R.
        rewrite (laplace_integral_strict_cdf 0 (4 / epsilon) threshold
          (query_scale_positive epsilon Hepsilon)).
        ring.
  }
  rewrite Hnoisy1.
  ring.
Qed.

(** It is convenient for the remaining calculation to use the paper's rate
    parameter [a = epsilon/4]. *)
Definition laplace_cdf_rate (location rate cutoff : R) : R :=
  if Rle_dec cutoff location
  then ((1 / 2) * exp (rate * (cutoff - location)))%R
  else (1 - (1 / 2) * exp (- rate * (cutoff - location)))%R.

Definition threshold_integrand_rate (rate threshold : R) : R :=
  rate * exp (- 2 * rate * Rabs threshold) *
  laplace_cdf_rate 0 rate threshold *
  (1 - laplace_cdf_rate 1 rate threshold).

Lemma laplace_cdf_rate_left :
  forall location rate cutoff : R,
    (cutoff <= location)%R ->
    laplace_cdf_rate location rate cutoff =
      ((1 / 2) * exp (rate * (cutoff - location)))%R.
Proof.
  intros location rate cutoff Hle.
  unfold laplace_cdf_rate.
  destruct (Rle_dec cutoff location); [reflexivity | contradiction].
Qed.

Lemma laplace_cdf_rate_right :
  forall location rate cutoff : R,
    (location <= cutoff)%R ->
    laplace_cdf_rate location rate cutoff =
      (1 - (1 / 2) * exp (- rate * (cutoff - location)))%R.
Proof.
  intros location rate cutoff Hle.
  unfold laplace_cdf_rate.
  destruct (Rle_dec cutoff location) as [Hreverse | Hstrict].
  - assert (cutoff = location) by lra.
    subst cutoff.
    rewrite Rminus_diag, Rmult_0_r, exp_0.
    rewrite Rmult_0_r, exp_0.
    pose proof (Rplus_half_diag 1) as Hhalf.
    lra.
  - reflexivity.
Qed.

Lemma laplace_cdf_scale_as_rate :
  forall (epsilon location cutoff : R),
    epsilon <> 0%R ->
    laplace_cdf location (4 / epsilon) cutoff =
      laplace_cdf_rate location (epsilon / 4) cutoff.
Proof.
  intros epsilon location cutoff Hepsilon.
  unfold laplace_cdf, laplace_cdf_rate.
  destruct (Rle_dec cutoff location) as [Hle | Hnle].
  - replace ((cutoff - location) / (4 / epsilon))
      with ((epsilon / 4) * (cutoff - location)) by
        (field; exact Hepsilon).
    reflexivity.
  - replace (- (cutoff - location) / (4 / epsilon))
      with (- (epsilon / 4) * (cutoff - location)) by
        (field; exact Hepsilon).
    reflexivity.
Qed.

Lemma threshold_integrand_as_rate :
  forall (epsilon threshold : R),
    epsilon <> 0%R ->
    threshold_integrand epsilon threshold =
      threshold_integrand_rate (epsilon / 4) threshold.
Proof.
  intros epsilon threshold Hepsilon.
  unfold threshold_integrand, threshold_integrand_rate,
    laplace_density_R.
  rewrite (laplace_cdf_scale_as_rate epsilon 0 threshold Hepsilon).
  rewrite (laplace_cdf_scale_as_rate epsilon 1 threshold Hepsilon).
  assert (Hcoefficient :
    ((1 / (2 * (2 / epsilon))) = epsilon / 4)%R).
  { field; exact Hepsilon. }
  assert (Hexponent :
    ((- Rabs (threshold - 0) / (2 / epsilon)) =
      (- 2 * (epsilon / 4) * Rabs threshold))%R).
  {
    rewrite Rminus_0_r.
    field; exact Hepsilon.
  }
  rewrite Hcoefficient, Hexponent.
  ring.
Qed.

Lemma integrand_rate_below_pointwise :
  forall rate threshold : R,
    (threshold < 0)%R ->
    threshold_integrand_rate rate threshold =
      ((rate / 2) * exp ((3 * rate) * threshold) +
       (- rate / 4 * exp (- rate)) * exp ((4 * rate) * threshold))%R.
Proof.
  intros rate threshold Hthreshold.
  unfold threshold_integrand_rate.
  rewrite (Rabs_left threshold Hthreshold).
  rewrite (laplace_cdf_rate_left 0 rate threshold) by lra.
  rewrite (laplace_cdf_rate_left 1 rate threshold) by lra.
  rewrite Rminus_0_r.
  assert (Hexp3 :
    (exp (- 2 * rate * - threshold) * exp (rate * threshold) =
      exp ((3 * rate) * threshold))%R).
  {
    rewrite <- exp_plus.
    f_equal; ring.
  }
  assert (Hexp4 :
    (exp (- 2 * rate * - threshold) * exp (rate * threshold) *
      exp (rate * (threshold - 1)) =
      exp (- rate) * exp ((4 * rate) * threshold))%R).
  {
    rewrite <- exp_plus, <- exp_plus, <- exp_plus.
    f_equal; ring.
  }
  transitivity
    (((rate / 2) *
        (exp (- 2 * rate * - threshold) * exp (rate * threshold))) +
      (- rate / 4) *
        (exp (- 2 * rate * - threshold) * exp (rate * threshold) *
          exp (rate * (threshold - 1))))%R.
  - field.
  - rewrite Hexp4, Hexp3.
    field.
Qed.

Lemma integrand_rate_between_pointwise :
  forall rate threshold : R,
    (0 <= threshold < 1)%R ->
    threshold_integrand_rate rate threshold =
      ((rate * (1 + exp (- rate) / 4)) *
          exp ((- 2 * rate) * threshold) +
       (- rate / 2) * exp ((- 3 * rate) * threshold) +
       (- rate / 2 * exp (- rate)) *
          exp ((- rate) * threshold))%R.
Proof.
  intros rate threshold Hthreshold.
  unfold threshold_integrand_rate.
  rewrite (Rabs_right threshold) by lra.
  rewrite (laplace_cdf_rate_right 0 rate threshold) by lra.
  rewrite (laplace_cdf_rate_left 1 rate threshold) by lra.
  rewrite Rminus_0_r.
  assert (Hexp3 :
    (exp (- 2 * rate * threshold) *
      exp (- rate * threshold) =
      exp ((- 3 * rate) * threshold))%R).
  {
    rewrite <- exp_plus.
    f_equal; ring.
  }
  assert (Hexp1 :
    (exp (- 2 * rate * threshold) *
      exp (rate * (threshold - 1)) =
      exp (- rate) * exp ((- rate) * threshold))%R).
  {
    rewrite <- exp_plus, <- exp_plus.
    f_equal; ring.
  }
  assert (Hexp0 :
    (exp (- 2 * rate * threshold) *
      exp (- rate * threshold) *
      exp (rate * (threshold - 1)) =
      exp (- rate) * exp ((- 2 * rate) * threshold))%R).
  {
    rewrite <- exp_plus, <- exp_plus, <- exp_plus.
    f_equal; ring.
  }
  transitivity
    ((rate * exp (- 2 * rate * threshold)) +
      (- rate / 2) *
        (exp (- 2 * rate * threshold) * exp (- rate * threshold)) +
      (- rate / 2) *
        (exp (- 2 * rate * threshold) * exp (rate * (threshold - 1))) +
      (rate / 4) *
        (exp (- 2 * rate * threshold) * exp (- rate * threshold) *
          exp (rate * (threshold - 1))))%R.
  - field.
  - rewrite Hexp0, Hexp3, Hexp1.
    field.
Qed.

Lemma integrand_rate_above_pointwise :
  forall rate threshold : R,
    (1 <= threshold)%R ->
    threshold_integrand_rate rate threshold =
      ((rate / 2 * exp rate) * exp ((- 3 * rate) * threshold) +
       (- rate / 4 * exp rate) * exp ((- 4 * rate) * threshold))%R.
Proof.
  intros rate threshold Hthreshold.
  unfold threshold_integrand_rate.
  rewrite (Rabs_right threshold) by lra.
  rewrite (laplace_cdf_rate_right 0 rate threshold) by lra.
  rewrite (laplace_cdf_rate_right 1 rate threshold) by lra.
  rewrite Rminus_0_r.
  assert (Hexp3 :
    (exp (- 2 * rate * threshold) *
      exp (- rate * (threshold - 1)) =
      exp rate * exp ((- 3 * rate) * threshold))%R).
  {
    rewrite <- exp_plus, <- exp_plus.
    f_equal; ring.
  }
  assert (Hexp4 :
    (exp (- 2 * rate * threshold) *
      exp (- rate * threshold) *
      exp (- rate * (threshold - 1)) =
      exp rate * exp ((- 4 * rate) * threshold))%R).
  {
    rewrite <- exp_plus, <- exp_plus, <- exp_plus.
    f_equal; ring.
  }
  transitivity
    (((rate / 2) *
        (exp (- 2 * rate * threshold) *
          exp (- rate * (threshold - 1)))) +
      (- rate / 4) *
        (exp (- 2 * rate * threshold) * exp (- rate * threshold) *
          exp (- rate * (threshold - 1))))%R.
  - field.
  - rewrite Hexp4, Hexp3.
    field.
Qed.

Lemma integral_rate_below :
  forall rate : R,
    (0 < rate)%R ->
    real_integral_below 0 (threshold_integrand_rate rate) =
      (1 / 6 - exp (- rate) / 16)%R.
Proof.
  intros rate Hrate.
  transitivity
    (real_integral_below 0
      (fun threshold =>
        (rate / 2) * exp ((3 * rate) * threshold) +
        (- rate / 4 * exp (- rate)) *
          exp ((4 * rate) * threshold))).
  - unfold real_integral_below.
    apply real_integral_extensional.
    intro threshold.
    destruct (Rlt_dec threshold 0) as [Hthreshold | Hthreshold].
    + rewrite (real_indicator_true _ Hthreshold).
      rewrite (integrand_rate_below_pointwise rate threshold Hthreshold).
      reflexivity.
    + rewrite (real_indicator_false (threshold < 0)%R) by exact Hthreshold.
      ring.
  - rewrite real_integral_below_add.
    rewrite !real_integral_below_scale.
    rewrite (real_integral_exp_below 0 (3 * rate)) by lra.
    rewrite (real_integral_exp_below 0 (4 * rate)) by lra.
    rewrite !Rmult_0_r, !exp_0.
    field; lra.
Qed.

Lemma integral_rate_between :
  forall rate : R,
    (0 < rate)%R ->
    real_integral_between 0 1 (threshold_integrand_rate rate) =
      (1 / 3 - 3 * exp (- rate) / 8 + exp (- 3 * rate) / 24)%R.
Proof.
  intros rate Hrate.
  transitivity
    (real_integral_between 0 1
      (fun threshold =>
        (rate * (1 + exp (- rate) / 4)) *
          exp ((- 2 * rate) * threshold) +
        (- rate / 2) * exp ((- 3 * rate) * threshold) +
        (- rate / 2 * exp (- rate)) *
          exp ((- rate) * threshold))).
  - unfold real_integral_between.
    apply real_integral_extensional.
    intro threshold.
    destruct (excluded_middle_informative (0 <= threshold < 1)%R)
      as [Hthreshold | Hthreshold].
    + rewrite (real_indicator_true _ Hthreshold).
      rewrite (integrand_rate_between_pointwise rate threshold Hthreshold).
      reflexivity.
    + rewrite (real_indicator_false (0 <= threshold < 1)%R) by
        exact Hthreshold.
      ring.
  - rewrite real_integral_between_add.
    rewrite real_integral_between_add.
    rewrite !real_integral_between_scale.
    rewrite (real_integral_exp_between 0 1 (- 2 * rate)) by lra.
    rewrite (real_integral_exp_between 0 1 (- 3 * rate)) by lra.
    rewrite (real_integral_exp_between 0 1 (- rate)) by lra.
    rewrite !Rmult_0_r, !exp_0, !Rmult_1_r.
    assert (Hexp2 :
      (exp (- rate) * exp (- rate) = exp (- 2 * rate))%R).
    {
      rewrite <- exp_plus.
      f_equal; ring.
    }
    assert (Hexp3 :
      (exp (- rate) * exp (- 2 * rate) = exp (- 3 * rate))%R).
    {
      rewrite <- exp_plus.
      f_equal; ring.
    }
    transitivity
      (((1 + exp (- rate) / 4) * (1 - exp (- 2 * rate)) / 2) +
        (exp (- 3 * rate) - 1) / 6 +
        exp (- rate) * (exp (- rate) - 1) / 2)%R.
    + field; lra.
    + transitivity
        ((1 / 3 - 3 * exp (- rate) / 8 - exp (- 2 * rate) / 2 +
          (exp (- rate) * exp (- rate)) / 2 -
          (exp (- rate) * exp (- 2 * rate)) / 8 +
          exp (- 3 * rate) / 6)%R).
      * field.
      * rewrite Hexp2, Hexp3.
        field.
Qed.

Lemma integral_rate_above :
  forall rate : R,
    (0 < rate)%R ->
    real_integral_above 1 (threshold_integrand_rate rate) =
      (exp (- 2 * rate) / 6 - exp (- 3 * rate) / 16)%R.
Proof.
  intros rate Hrate.
  transitivity
    (real_integral_above 1
      (fun threshold =>
        (rate / 2 * exp rate) * exp ((- 3 * rate) * threshold) +
        (- rate / 4 * exp rate) * exp ((- 4 * rate) * threshold))).
  - unfold real_integral_above.
    apply real_integral_extensional.
    intro threshold.
    destruct (Rle_dec 1 threshold) as [Hthreshold | Hthreshold].
    + rewrite (real_indicator_true _ Hthreshold).
      rewrite (integrand_rate_above_pointwise rate threshold Hthreshold).
      reflexivity.
    + rewrite (real_indicator_false (1 <= threshold)%R) by exact Hthreshold.
      ring.
  - rewrite real_integral_above_add.
    rewrite !real_integral_above_scale.
    rewrite (real_integral_exp_above 1 (- 3 * rate)) by lra.
    rewrite (real_integral_exp_above 1 (- 4 * rate)) by lra.
    rewrite !Rmult_1_r.
    assert (Hexp2 :
      (exp rate * exp (- 3 * rate) = exp (- 2 * rate))%R).
    {
      rewrite <- exp_plus.
      f_equal; ring.
    }
    assert (Hexp3 :
      (exp rate * exp (- 4 * rate) = exp (- 3 * rate))%R).
    {
      rewrite <- exp_plus.
      f_equal; ring.
    }
    transitivity
      ((exp rate * exp (- 3 * rate)) / 6 -
        (exp rate * exp (- 4 * rate)) / 16)%R.
    + field; lra.
    + rewrite Hexp2, Hexp3.
      reflexivity.
Qed.

Lemma threshold_integral_rate :
  forall rate : R,
    (0 < rate)%R ->
    real_integral (threshold_integrand_rate rate) =
      ((24 - 21 * exp (- rate) + 8 * exp (- 2 * rate) -
        exp (- 3 * rate)) / 48)%R.
Proof.
  intros rate Hrate.
  rewrite (real_integral_split_three
    (threshold_integrand_rate rate) 0 1) by lra.
  rewrite (integral_rate_below rate Hrate).
  rewrite (integral_rate_between rate Hrate).
  rewrite (integral_rate_above rate Hrate).
  field.
Qed.

Lemma rate_form_equals_closed_form :
  forall epsilon : R,
    epsilon <> 0%R ->
    ((24 - 21 * exp (- (epsilon / 4)) +
       8 * exp (- 2 * (epsilon / 4)) -
       exp (- 3 * (epsilon / 4))) / 48)%R =
      closed_form_probability epsilon.
Proof.
  intros epsilon Hepsilon.
  unfold closed_form_probability.
  assert (Hexp_nonzero : exp (3 * epsilon / 4) <> 0%R).
  { apply exp_neq_0. }
  assert (Hexp1 :
    (exp (- (epsilon / 4)) * exp (3 * epsilon / 4) =
      exp (epsilon / 2))%R).
  {
    rewrite <- exp_plus.
    f_equal; field; exact Hepsilon.
  }
  assert (Hexp2 :
    (exp (- 2 * (epsilon / 4)) * exp (3 * epsilon / 4) =
      exp (epsilon / 4))%R).
  {
    rewrite <- exp_plus.
    f_equal; field; exact Hepsilon.
  }
  assert (Hexp3 :
    (exp (- 3 * (epsilon / 4)) * exp (3 * epsilon / 4) = 1)%R).
  {
    rewrite <- exp_plus.
    replace (- 3 * (epsilon / 4) + 3 * epsilon / 4)%R with 0%R by
      (field; exact Hepsilon).
    apply exp_0.
  }
  assert (Hnumerator :
    (24 * exp (3 * epsilon / 4) - 1 + 8 * exp (epsilon / 4) -
      21 * exp (epsilon / 2) =
     exp (3 * epsilon / 4) *
       (24 - 21 * exp (- (epsilon / 4)) +
        8 * exp (- 2 * (epsilon / 4)) -
        exp (- 3 * (epsilon / 4))))%R).
  {
    transitivity
      (24 * exp (3 * epsilon / 4) -
        exp (- 3 * (epsilon / 4)) * exp (3 * epsilon / 4) +
        8 * (exp (- 2 * (epsilon / 4)) * exp (3 * epsilon / 4)) -
        21 * (exp (- (epsilon / 4)) * exp (3 * epsilon / 4)))%R.
    - rewrite Hexp1, Hexp2, Hexp3.
      ring.
    - ring.
  }
  rewrite Hnumerator.
  field; exact Hexp_nonzero.
Qed.

Theorem nested_integral_value :
  forall epsilon : R,
    (0 < epsilon)%R ->
    nested_integral epsilon = closed_form_probability epsilon.
Proof.
  intros epsilon Hepsilon.
  rewrite (nested_integral_reduce epsilon Hepsilon).
  transitivity
    (real_integral
      (threshold_integrand_rate (epsilon / 4))).
  - apply real_integral_extensional.
    intro threshold.
    apply threshold_integrand_as_rate.
    lra.
  - rewrite (threshold_integral_rate (epsilon / 4)) by lra.
    apply rate_form_equals_closed_form.
    lra.
Qed.

(** Hoare-logic plumbing.  These abbreviations keep the weakest
    preconditions generated by the unfolded conditionals readable. *)
Definition event_probability (r : R) (gamma : CFormula) : PFormula :=
  [[ $(r) = Pr[$(gamma)] ]].

Definition rigid_constant
  (y : ProbLogicVar) (r : R) : PFormula :=
  [[ y = $(r) ]].

Lemma rigid_constant_analytical :
  forall (y : ProbLogicVar) (r : R),
    pformula_analytical (rigid_constant y r).
Proof.
  intros y r.
  cbn [rigid_constant p_eq p_and p_not
    pformula_analytical pterm_analytical].
  tauto.
Qed.

Lemma add_rigid_constant :
  forall (eta : PFormula) (s : Cmd) (gamma : CFormula)
    (y : ProbLogicVar) (r : R),
    {{ $(eta) }} $(s) {{ $(event_probability r gamma) }} ->
    {{ $(eta) /\ $(rigid_constant y r) }} $(s)
      {{ y = Pr[$(gamma)] }}.
Proof.
  intros eta s gamma y r Hbranch.
  assert (Hevent :
    {{ $(eta) /\ $(rigid_constant y r) }} $(s)
      {{ $(event_probability r gamma) }}).
  {
    eapply HConseq with
      (eta1 := eta) (eta2 := event_probability r gamma).
    - unfold pformula_valid.
      intro ps.
      cbn [p_and p_not psatisfies].
      tauto.
    - exact Hbranch.
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
  }
  assert (Hrigid :
    {{ $(eta) /\ $(rigid_constant y r) }} $(s)
      {{ $(rigid_constant y r) }}).
  {
    eapply HConseq with
      (eta1 := rigid_constant y r)
      (eta2 := rigid_constant y r).
    - unfold pformula_valid.
      intro ps.
      cbn [p_and p_not psatisfies].
      tauto.
    - apply HFree.
      apply rigid_constant_analytical.
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
  }
  eapply HConseq with
    (eta1 := [[ $(eta) /\ $(rigid_constant y r) ]])
    (eta2 := [[ $(event_probability r gamma) /\
      $(rigid_constant y r) ]]).
  - unfold pformula_valid.
    intro ps; cbn [psatisfies]; tauto.
  - apply HAnd; assumption.
  - unfold pformula_valid, event_probability, rigid_constant.
    intro ps.
    cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
    intuition lra.
Qed.

(** A local exact conditional rule.  The rigid variables record the two
    branch masses, [HIfEq] adds them, [HFree]/[HAnd] retain their constant
    values, and [HElimv] removes the auxiliary names. *)
Lemma if_constants :
  forall (eta1 eta2 : PFormula) (guard gamma : CFormula)
    (s1 s2 : Cmd) (r1 r2 : R),
    {{ $(eta1) }} $(s1) {{ $(event_probability r1 gamma) }} ->
    {{ $(eta2) }} $(s2) {{ $(event_probability r2 gamma) }} ->
    {{ $(subst_prob_pformula y_then [[ $(r1) ]]
          (subst_prob_pformula y_else [[ $(r2) ]]
            (if_precondition eta1 eta2 guard))) }}
      if $(guard) then $(s1) else $(s2) end
    {{ $(event_probability (r1 + r2) gamma) }}.
Proof.
  intros eta1 eta2 guard gamma s1 s2 r1 r2 Hbranch1 Hbranch2.
  set (base := if_precondition eta1 eta2 guard).
  set (eq1 := rigid_constant y_then r1).
  set (eq2 := rigid_constant y_else r2).
  assert (Hif :
    {{ $(if_precondition [[ $(eta1) /\ $(eq1) ]]
          [[ $(eta2) /\ $(eq2) ]] guard) }}
      if $(guard) then $(s1) else $(s2) end
    {{ y_then + y_else = Pr[$(gamma)] }}).
  {
    apply HIfEq with
      (eta1 := [[ $(eta1) /\ $(eq1) ]])
      (eta2 := [[ $(eta2) /\ $(eq2) ]]).
    - unfold eq1.
      apply add_rigid_constant.
      exact Hbranch1.
    - unfold eq2.
      apply add_rigid_constant.
      exact Hbranch2.
  }
  set (with_constants := [[ ($(base) /\ $(eq1)) /\ $(eq2) ]]).
  assert (Hif_from_constants :
    {{ $(with_constants) }}
      if $(guard) then $(s1) else $(s2) end
    {{ y_then + y_else = Pr[$(gamma)] }}).
  {
    eapply HConseq with
      (eta1 := if_precondition [[ $(eta1) /\ $(eq1) ]]
        [[ $(eta2) /\ $(eq2) ]] guard)
      (eta2 := [[ y_then + y_else = Pr[$(gamma)] ]]).
    - unfold pformula_valid, with_constants, base, eq1, eq2,
        if_precondition, rigid_constant.
      intro ps.
      cbn [condition_pformula condition_pterm p_and p_not p_eq
        psatisfies pterm_eval] in *.
      intuition lra.
    - exact Hif.
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
  }
  assert (Hconstants :
    {{ $(with_constants) }}
      if $(guard) then $(s1) else $(s2) end
    {{ $(eq1) /\ $(eq2) }}).
  {
    eapply HConseq with
      (eta1 := [[ $(eq1) /\ $(eq2) ]])
      (eta2 := [[ $(eq1) /\ $(eq2) ]]).
    - unfold pformula_valid, with_constants.
      intro ps.
      cbn [p_and p_not psatisfies].
      tauto.
    - apply HFree.
      unfold eq1, eq2.
      cbn [rigid_constant p_eq p_and p_not
        pformula_analytical pterm_analytical].
      tauto.
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
  }
  assert (Hwithout_rigids :
    {{ $(with_constants) }}
      if $(guard) then $(s1) else $(s2) end
    {{ $(event_probability (r1 + r2) gamma) }}).
  {
    eapply HConseq with
      (eta1 := with_constants)
      (eta2 := [[
        (y_then + y_else = Pr[$(gamma)]) /\ $(eq1) /\ $(eq2)
      ]]).
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
    - apply HAnd; assumption.
    - unfold pformula_valid, event_probability, eq1, eq2,
        rigid_constant.
      intro ps.
      cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
      intuition lra.
  }
  assert (Helim_else :
    {{ $(subst_prob_pformula y_else [[ $(r2) ]]
          [[ $(base) /\ $(eq1) ]]) }}
      if $(guard) then $(s1) else $(s2) end
    {{ $(event_probability (r1 + r2) gamma) }}).
  {
    eapply HElimv with
      (eta1 := [[ $(base) /\ $(eq1) ]])
      (y := y_else) (p := [[ $(r2) ]]).
    - change ({{ $(with_constants) }}
        if $(guard) then $(s1) else $(s2) end
        {{ $(event_probability (r1 + r2) gamma) }}).
      exact Hwithout_rigids.
    - cbn [prob_logic_var_occurs_pterm]; tauto.
    - cbn [event_probability p_eq p_and p_not
        prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm].
      tauto.
  }
  assert (Helim_then :
    {{ $(subst_prob_pformula y_then [[ $(r1) ]]
          (subst_prob_pformula y_else [[ $(r2) ]] base)) }}
      if $(guard) then $(s1) else $(s2) end
    {{ $(event_probability (r1 + r2) gamma) }}).
  {
    eapply HElimv with
      (eta1 := subst_prob_pformula y_else [[ $(r2) ]] base)
      (y := y_then) (p := [[ $(r1) ]]).
    - change ({{ $(subst_prob_pformula y_else [[ $(r2) ]]
          [[ $(base) /\ $(eq1) ]]) }}
        if $(guard) then $(s1) else $(s2) end
        {{ $(event_probability (r1 + r2) gamma) }}).
      exact Helim_else.
    - cbn [prob_logic_var_occurs_pterm]; tauto.
    - cbn [event_probability p_eq p_and p_not
        prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm].
      tauto.
  }
  unfold base in Helim_then.
  exact Helim_then.
Qed.

Lemma laplace_constant_valid :
  forall (location : Term) (scale : R),
    (0 < scale)%R ->
    pformula_valid
      [[ almost_sure[$(distribution_valid_formula
          <{ laplace ( $(location), $(scale) ) }>)] ]].
Proof.
  intros location scale Hscale.
  unfold pformula_valid.
  intro ps.
  assert (Heq :
    expectation (pstate_measure ps)
      (q_eval
        [[ indicator[$(distribution_valid_formula
          <{ laplace ( $(location), $(scale) ) }>)] ]]) =
    expectation (pstate_measure ps) (q_eval [[ indicator[true] ]])).
  {
    rewrite !expectation_indicator.
    apply measure_extensional.
    intro v.
    unfold formula_assertion, distribution_valid_formula, c_lt, c_not,
      c_true.
    cbn [satisfies term_eval].
    split.
    - intros _ Hfalse; exact Hfalse.
    - intros _ Hle; lra.
  }
  unfold p_almost_sure, p_eq, p_and, p_not.
  cbn [psatisfies pterm_eval].
  lra.
Qed.

Lemma laplace_sample :
  forall (eta : PFormula) (x : RealProgramVar) (location : Term)
    (scale : R),
    (0 < scale)%R ->
    {{ $(sample_pformula x <{ laplace ( $(location), $(scale) ) }> eta) }}
      x sample laplace ( $(location), $(scale) )
    {{ $(eta) }}.
Proof.
  intros eta x location scale Hscale.
  apply HRealSample.
  - unfold pformula_valid.
    intro ps; cbn [psatisfies]; tauto.
  - unfold pformula_valid.
    intro ps.
    cbn [psatisfies].
    intro Hpre.
    apply (laplace_constant_valid location scale Hscale ps).
Qed.

Definition output_probability (r : R) : PFormula :=
  event_probability r bot_top.

Definition inner_true_pre (p : R) : PFormula :=
  subst_bool_pformula out2 <{ true }> (output_probability p).

Definition inner_false_pre : PFormula :=
  output_probability 0.

Definition inner_if_pre (p : R) : PFormula :=
  subst_prob_pformula y_then [[ $(p) ]]
    (subst_prob_pformula y_else [[ 0 ]]
      (if_precondition (inner_true_pre p) inner_false_pre
        <{ above2 }>)).

Definition after_noisy2 (p : R) : PFormula :=
  subst_bool_pformula above2 second_comparison
    (inner_if_pre p).

Definition before_noisy2 (epsilon p : R) : PFormula :=
  sample_pformula noisy2
    (query_distribution epsilon q2)
    (after_noisy2 p).

Lemma inner_if_derivable :
  forall p : R,
    {{ $(inner_if_pre p) }}
      if above2 then out2 b= true else skip end
    {{ $(output_probability p) }}.
Proof.
  intro p.
  unfold inner_if_pre, output_probability.
  replace p with (p + 0)%R at 3 by ring.
  apply if_constants.
  - unfold inner_true_pre.
    apply HBoolAssign.
  - unfold inner_false_pre.
    apply HSkip.
Qed.

Lemma second_iteration_derivable :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(before_noisy2 epsilon p) }}
      $(second_iteration epsilon)
    {{ $(output_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold second_iteration, before_noisy2,
    query_distribution.
  eapply HSeq with (eta2 := after_noisy2 p).
  - apply laplace_sample.
    apply query_scale_positive; exact Hepsilon.
  - eapply HSeq with (eta2 := inner_if_pre p).
    + unfold after_noisy2.
      apply HBoolAssign.
    + apply inner_if_derivable.
Qed.

Definition outer_true_pre : PFormula :=
  subst_bool_pformula out1 <{ true }> (output_probability 0).

Definition outer_if_pre (epsilon p : R) : PFormula :=
  subst_prob_pformula y_then [[ 0 ]]
    (subst_prob_pformula y_else [[ $(p) ]]
      (if_precondition outer_true_pre
        (before_noisy2 epsilon p) <{ above1 }>)).

Definition after_noisy1 (epsilon p : R) : PFormula :=
  subst_bool_pformula above1 first_comparison
    (outer_if_pre epsilon p).

Definition before_noisy1 (epsilon p : R) : PFormula :=
  sample_pformula noisy1
    (query_distribution epsilon q1)
    (after_noisy1 epsilon p).

Definition before_threshold (epsilon p : R) : PFormula :=
  sample_pformula threshold (threshold_distribution epsilon)
    (before_noisy1 epsilon p).

Definition before_output2 (epsilon p : R) : PFormula :=
  subst_bool_pformula out2 <{ false }>
    (before_threshold epsilon p).

Definition generic_pre (epsilon p : R) : PFormula :=
  subst_bool_pformula out1 <{ false }>
    (before_output2 epsilon p).

Lemma outer_if_derivable :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(outer_if_pre epsilon p) }}
      if above1 then out1 b= true
      else $(second_iteration epsilon)
      end
    {{ $(output_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold outer_if_pre, output_probability.
  replace p with (0 + p)%R at 3 by ring.
  apply if_constants.
  - unfold outer_true_pre.
    apply HBoolAssign.
  - apply second_iteration_derivable.
    exact Hepsilon.
Qed.

Theorem generic_wp_derivable :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(generic_pre epsilon p) }}
      $(two_queries epsilon)
    {{ $(output_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold two_queries, generic_pre.
  eapply HSeq with (eta2 := before_output2 epsilon p).
  - apply HBoolAssign.
  - eapply HSeq with (eta2 := before_threshold epsilon p).
    + unfold before_output2.
      apply HBoolAssign.
    + eapply HSeq with (eta2 := before_noisy1 epsilon p).
      * unfold before_threshold, threshold_distribution.
        apply laplace_sample.
        apply threshold_scale_positive; exact Hepsilon.
      * eapply HSeq with (eta2 := after_noisy1 epsilon p).
        -- unfold before_noisy1, query_distribution.
           apply laplace_sample.
           apply query_scale_positive; exact Hepsilon.
        -- eapply HSeq with (eta2 := outer_if_pre epsilon p).
           ++ unfold after_noisy1.
              apply HBoolAssign.
           ++ apply outer_if_derivable.
              exact Hepsilon.
Qed.

Definition concrete_pre (epsilon p : R) : PFormula :=
  subst_real_pformula q1 <{ 0 }>
    (subst_real_pformula q2 <{ 1 }>
      (generic_pre epsilon p)).

Theorem concrete_wp_derivable :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(concrete_pre epsilon p) }}
      $(run_01 epsilon)
    {{ $(output_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold run_01, concrete_pre.
  eapply HSeq with
    (eta2 := subst_real_pformula q2 <{ 1 }>
      (generic_pre epsilon p)).
  - apply HRealAssign.
  - eapply HSeq with (eta2 := generic_pre epsilon p).
    + apply HRealAssign.
    + apply generic_wp_derivable.
      exact Hepsilon.
Qed.

Lemma path_integral_01_eval :
  forall (epsilon : R) (v : state),
    q_eval (path_integral_01 epsilon) v =
      nested_integral epsilon.
Proof.
  intros epsilon v.
  unfold path_integral_01, nested_integral,
    laplace_density_R, threshold_distribution,
    query_distribution, path_event, c_and, c_not, c_lt.
  cbn [q_eval distribution_density term_eval satisfies update_real
    real_program_values].
  apply real_integral_extensional.
  intro threshold.
  f_equal.
  apply real_integral_extensional.
  intro noisy1.
  f_equal.
  apply real_integral_extensional.
  intro noisy2.
  f_equal.
  apply real_indicator_extensional.
  unfold SVT_notation.threshold, SVT_notation.noisy1,
    SVT_notation.noisy2.
  cbn [satisfies c_not term_eval update_real update_real_values
    real_program_values real_program_var_eq_dec].
  change
    (((((threshold <= noisy1)%R -> False) ->
        (threshold <= noisy2)%R -> False) -> False) <->
      ((noisy1 < threshold)%R /\ (threshold <= noisy2)%R)).
  split.
  - intro H.
    split; lra.
  - intros [Hlt Hle] Hnot.
    apply Hnot; [lra | exact Hle].
Qed.

Definition symbolic_pre (epsilon p : R) : PFormula :=
  [[ $(normalized) /\ E[$(path_integral epsilon)] = $(p) ]].

(** The three expectation constructs occurring in the generated weakest
    precondition: an impossible first-true branch, the desired path, and an
    impossible second-false branch. *)
Definition wp_outer_zero_construct (epsilon : R) : PConstruct :=
  subst_bool_pconstruct out1 <{ false }>
    (subst_bool_pconstruct out2 <{ false }>
      [[
        integral threshold ~ $(threshold_distribution epsilon),
        integral noisy1 ~ $(query_distribution epsilon q1),
        $(subst_bool_pconstruct above1 first_comparison
          (condition_pconstruct
            [[ indicator[$(subst_bool_cformula out1 <{ true }> bot_top)] ]]
            <{ above1 }>))
      ]]).

Definition wp_path_construct (epsilon : R) : PConstruct :=
  subst_bool_pconstruct out1 <{ false }>
    (subst_bool_pconstruct out2 <{ false }>
      [[
        integral threshold ~ $(threshold_distribution epsilon),
        integral noisy1 ~ $(query_distribution epsilon q1),
        $(subst_bool_pconstruct above1 first_comparison
          (condition_pconstruct
            [[
              integral noisy2 ~ $(query_distribution epsilon q2),
              $(subst_bool_pconstruct above2 second_comparison
                (condition_pconstruct
                  [[ indicator[$(subst_bool_cformula
                    out2 <{ true }> bot_top)] ]]
                  <{ above2 }>))
            ]]
            <{ ~ above1 }>))
      ]]).

Definition wp_inner_zero_construct (epsilon : R) : PConstruct :=
  subst_bool_pconstruct out1 <{ false }>
    (subst_bool_pconstruct out2 <{ false }>
      [[
        integral threshold ~ $(threshold_distribution epsilon),
        integral noisy1 ~ $(query_distribution epsilon q1),
        $(subst_bool_pconstruct above1 first_comparison
          (condition_pconstruct
            [[
              integral noisy2 ~ $(query_distribution epsilon q2),
              $(subst_bool_pconstruct above2 second_comparison
                (condition_pconstruct
                  [[ indicator[$(bot_top)] ]]
                  <{ ~ above2 }>))
            ]]
            <{ ~ above1 }>))
      ]]).

Lemma generic_pre_shape :
  forall epsilon p : R,
    generic_pre epsilon p =
      [[ 0 = E[$(wp_outer_zero_construct epsilon)] /\
         $(p) = E[$(wp_path_construct epsilon)] /\
         0 = E[$(wp_inner_zero_construct epsilon)] ]].
Proof.
  intros epsilon p.
  unfold generic_pre, before_output2, before_threshold,
    before_noisy1, after_noisy1, outer_if_pre,
    outer_true_pre, before_noisy2, after_noisy2,
    inner_if_pre, inner_true_pre, inner_false_pre,
    output_probability, event_probability,
    wp_outer_zero_construct, wp_path_construct,
    wp_inner_zero_construct, if_precondition.
  cbn [subst_prob_pformula subst_prob_pterm condition_pformula
    condition_pterm sample_pformula sample_pterm subst_bool_pformula
    subst_bool_pterm].
  reflexivity.
Qed.

Lemma wp_path_construct_eval :
  forall (epsilon : R) (v : state),
    q_eval (wp_path_construct epsilon) v =
      q_eval (path_integral epsilon) v.
Proof.
  intros epsilon v.
  unfold wp_path_construct, path_integral,
    threshold_distribution, query_distribution,
    first_comparison, second_comparison, bot_top,
    path_event, q1, q2, threshold, noisy1,
    noisy2, above1, above2, out1, out2.
  cbn [subst_bool_pconstruct subst_bool_cformula
    condition_pconstruct condition_pconstruct_fuel
    cformula_real_program_vars pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars pconstruct_size
    List.in_dec real_program_var_eq_dec bool_program_var_eq_dec
    q_eval distribution_density term_eval satisfies update_real
    update_real_values real_program_values c_and c_not c_lt c_true].
  apply real_integral_extensional.
  intro threshold.
  f_equal.
  apply real_integral_extensional.
  intro noisy1.
  f_equal.
  apply real_integral_extensional.
  intro noisy2.
  f_equal.
  apply real_indicator_extensional.
  repeat match goal with
  | |- context [bool_program_var_eq_dec ?x ?y] =>
      destruct (bool_program_var_eq_dec x y); try congruence
  end.
  cbn [subst_bool_cformula satisfies c_and c_not c_true term_eval
    update_real update_real_values real_program_values
    real_program_var_eq_dec].
  repeat match goal with
  | |- context [real_program_var_eq_dec ?x ?y] =>
      destruct (real_program_var_eq_dec x y); try congruence
  end.
  cbn [satisfies c_and c_not c_true term_eval update_real
    update_real_values real_program_values].
  tauto.
Qed.

Lemma wp_outer_zero_construct_eval :
  forall (epsilon : R) (v : state),
    q_eval (wp_outer_zero_construct epsilon) v = 0%R.
Proof.
  intros epsilon v.
  unfold wp_outer_zero_construct, threshold_distribution,
    query_distribution, first_comparison, bot_top,
    q1, threshold, noisy1, above1,
    out1, out2.
  cbn [subst_bool_pconstruct subst_bool_cformula
    condition_pconstruct condition_pconstruct_fuel
    cformula_real_program_vars pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars pconstruct_size
    List.in_dec real_program_var_eq_dec bool_program_var_eq_dec
    q_eval distribution_density term_eval satisfies update_real
    update_real_values real_program_values c_and c_not c_lt c_true].
  transitivity (real_integral (fun _ : R => 0%R)).
  - apply real_integral_extensional.
    intro threshold.
    match goal with
    | |- ?coefficient * ?inner = 0 =>
        enough (Hinner : inner = 0%R) by (rewrite Hinner; ring)
    end.
    transitivity (real_integral (fun _ : R => 0%R)).
    + apply real_integral_extensional.
      intro noisy1.
      f_equal.
      rewrite real_indicator_false.
      * ring.
      * repeat match goal with
        | |- context [bool_program_var_eq_dec ?x ?y] =>
            destruct (bool_program_var_eq_dec x y); try congruence
        end.
        cbn [subst_bool_cformula satisfies c_and c_not c_true term_eval
          update_real update_real_values real_program_values].
        repeat match goal with
        | |- context [real_program_var_eq_dec ?x ?y] =>
            destruct (real_program_var_eq_dec x y); try congruence
        end.
        cbn [satisfies c_and c_not c_true term_eval update_real
          update_real_values real_program_values].
        tauto.
    + apply real_integral_zero.
  - apply real_integral_zero.
Qed.

Lemma wp_inner_zero_construct_eval :
  forall (epsilon : R) (v : state),
    q_eval (wp_inner_zero_construct epsilon) v = 0%R.
Proof.
  intros epsilon v.
  unfold wp_inner_zero_construct, threshold_distribution,
    query_distribution, first_comparison, second_comparison,
    bot_top, q1, q2, threshold, noisy1,
    noisy2, above1, above2, out1, out2.
  cbn [subst_bool_pconstruct subst_bool_cformula
    condition_pconstruct condition_pconstruct_fuel
    cformula_real_program_vars pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars pconstruct_size
    List.in_dec real_program_var_eq_dec bool_program_var_eq_dec
    q_eval distribution_density term_eval satisfies update_real
    update_real_values real_program_values c_and c_not c_lt c_true].
  transitivity (real_integral (fun _ : R => 0%R)).
  - apply real_integral_extensional.
    intro threshold.
    match goal with
    | |- ?coefficient * ?inner = 0 =>
        enough (Hinner : inner = 0%R) by (rewrite Hinner; ring)
    end.
    transitivity (real_integral (fun _ : R => 0%R)).
    + apply real_integral_extensional.
      intro noisy1.
      match goal with
      | |- ?coefficient * ?inner = 0 =>
          enough (Hinner : inner = 0%R) by (rewrite Hinner; ring)
      end.
      transitivity (real_integral (fun _ : R => 0%R)).
      * apply real_integral_extensional.
        intro noisy2.
        f_equal.
        rewrite real_indicator_false.
        -- ring.
        -- repeat match goal with
           | |- context [bool_program_var_eq_dec ?x ?y] =>
               destruct (bool_program_var_eq_dec x y); try congruence
           end.
           cbn [subst_bool_cformula satisfies c_and c_not c_true term_eval
             update_real update_real_values real_program_values].
           repeat match goal with
           | |- context [real_program_var_eq_dec ?x ?y] =>
               destruct (real_program_var_eq_dec x y); try congruence
           end.
           cbn [satisfies c_and c_not c_true term_eval update_real
             update_real_values real_program_values].
           tauto.
      * apply real_integral_zero.
    + apply real_integral_zero.
  - apply real_integral_zero.
Qed.

Lemma symbolic_pre_implies_wp :
  forall epsilon p : R,
    pformula_valid
      [[ $(symbolic_pre epsilon p) -> $(generic_pre epsilon p) ]].
Proof.
  intros epsilon p.
  unfold pformula_valid.
  intro ps.
  rewrite generic_pre_shape.
  assert (Houter_zero :
    expectation (pstate_measure ps)
      (q_eval (wp_outer_zero_construct epsilon)) = 0%R).
  {
    transitivity
      (expectation (pstate_measure ps) (fun _ : state => 0%R)).
    - apply expectation_extensional.
      intro v; apply wp_outer_zero_construct_eval.
    - apply expectation_zero.
  }
  assert (Hinner_zero :
    expectation (pstate_measure ps)
      (q_eval (wp_inner_zero_construct epsilon)) = 0%R).
  {
    transitivity
      (expectation (pstate_measure ps) (fun _ : state => 0%R)).
    - apply expectation_extensional.
      intro v; apply wp_inner_zero_construct_eval.
    - apply expectation_zero.
  }
  assert (Hpath :
    expectation (pstate_measure ps)
      (q_eval (wp_path_construct epsilon)) =
    expectation (pstate_measure ps)
      (q_eval (path_integral epsilon))).
  {
    apply expectation_extensional.
    intro v; apply wp_path_construct_eval.
  }
  unfold symbolic_pre, normalized.
  cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
  intuition lra.
Qed.

Theorem symbolic_hoare :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(symbolic_pre epsilon p) }}
      $(two_queries epsilon)
    {{ $(bot_top_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  eapply HConseq with
    (eta1 := generic_pre epsilon p)
    (eta2 := output_probability p).
  - apply symbolic_pre_implies_wp.
  - apply generic_wp_derivable.
    exact Hepsilon.
  - unfold pformula_valid, output_probability,
      event_probability, bot_top_probability.
    intro ps.
    cbn [p_eq p_and p_not psatisfies pterm_eval] in *.
    intuition lra.
Qed.

Definition symbolic_concrete_pre (epsilon p : R) : PFormula :=
  subst_real_pformula q1 <{ 0 }>
    (subst_real_pformula q2 <{ 1 }>
      (symbolic_pre epsilon p)).

Theorem symbolic_concrete_hoare :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(symbolic_concrete_pre epsilon p) }}
      $(run_01 epsilon)
    {{ $(bot_top_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold run_01, symbolic_concrete_pre.
  eapply HSeq with
    (eta2 := subst_real_pformula q2 <{ 1 }>
      (symbolic_pre epsilon p)).
  - apply HRealAssign.
  - eapply HSeq with (eta2 := symbolic_pre epsilon p).
    + apply HRealAssign.
    + apply symbolic_hoare.
      exact Hepsilon.
Qed.

Lemma path_substitution_01 :
  forall epsilon : R,
    subst_real_pconstruct q1 <{ 0 }>
      (subst_real_pconstruct q2 <{ 1 }>
        (path_integral epsilon)) =
      path_integral_01 epsilon.
Proof.
  intro epsilon.
  unfold path_integral, path_integral_01,
    threshold_distribution, query_distribution,
    q1, q2, threshold, noisy1, noisy2.
  cbn [subst_real_pconstruct subst_real_pconstruct_fuel
    subst_real_distribution subst_real_term subst_real_cformula
    pconstruct_size pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars
    cformula_real_program_vars List.in_dec real_program_var_eq_dec].
  reflexivity.
Qed.

Lemma symbolic_concrete_pre_shape :
  forall epsilon p : R,
    symbolic_concrete_pre epsilon p =
      [[ $(normalized) /\
         E[$(subst_real_pconstruct q1 <{ 0 }>
           (subst_real_pconstruct q2 <{ 1 }>
             (path_integral epsilon)))] = $(p) ]].
Proof.
  intros epsilon p.
  unfold symbolic_concrete_pre, symbolic_pre, normalized.
  cbn [subst_real_pformula subst_real_pterm].
  reflexivity.
Qed.

Lemma normalized_implies_concrete_pre :
  forall epsilon : R,
    (0 < epsilon)%R ->
    pformula_valid
      [[ $(normalized) ->
         $(symbolic_concrete_pre epsilon
           (closed_form_probability epsilon)) ]].
Proof.
  intros epsilon Hepsilon.
  unfold pformula_valid.
  intro ps.
  rewrite symbolic_concrete_pre_shape.
  rewrite path_substitution_01.
  assert (Hpath :
    expectation (pstate_measure ps)
      (q_eval (path_integral_01 epsilon)) =
    (closed_form_probability epsilon *
      expectation (pstate_measure ps) (q_eval [[ indicator[true] ]]))%R).
  {
    transitivity
      (expectation (pstate_measure ps)
        (fun _ : state => closed_form_probability epsilon)).
    - apply expectation_extensional.
      intro v.
      rewrite path_integral_01_eval.
      apply nested_integral_value.
      exact Hepsilon.
    - apply expectation_constant.
  }
  unfold normalized.
  cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
  intro Hnormalized.
  assert (Hmass_upper :
    (expectation (pstate_measure ps) (q_eval [[ indicator[true] ]]) <= 1)%R).
  {
    apply NNPP; intro Hnot.
    apply Hnormalized.
    intro Hupper; contradiction.
  }
  assert (Hmass_lower :
    (1 <= expectation (pstate_measure ps) (q_eval [[ indicator[true] ]]))%R).
  {
    apply NNPP; intro Hnot.
    apply Hnormalized.
    intros Hupper Hlower; contradiction.
  }
  assert (Hmass :
    expectation (pstate_measure ps) (q_eval [[ indicator[true] ]]) = 1%R)
    by lra.
  assert (Hpath_value :
    expectation (pstate_measure ps) (q_eval (path_integral_01 epsilon)) =
      closed_form_probability epsilon).
  {
    rewrite Hpath, Hmass; ring.
  }
  assert (Hpath_upper :
    (expectation (pstate_measure ps)
      (q_eval (path_integral_01 epsilon)) <= closed_form_probability epsilon)%R)
    by lra.
  assert (Hpath_lower :
    (closed_form_probability epsilon <= expectation (pstate_measure ps)
      (q_eval (path_integral_01 epsilon)))%R)
    by lra.
  tauto.
Qed.

Theorem run_01_bot_top_probability :
  forall epsilon : R,
    (0 < epsilon)%R ->
    {{ $(normalized) }}
      $(run_01 epsilon)
    {{ $(bot_top_probability (closed_form_probability epsilon)) }}.
Proof.
  intros epsilon Hepsilon.
  eapply HConseq with
    (eta1 := symbolic_concrete_pre epsilon (closed_form_probability epsilon))
    (eta2 := bot_top_probability (closed_form_probability epsilon)).
  - apply normalized_implies_concrete_pre.
    exact Hepsilon.
  - apply symbolic_concrete_hoare.
    exact Hepsilon.
  - unfold pformula_valid.
    intro ps; cbn [psatisfies]; tauto.
Qed.

(** * The concrete input [[1, 1]]

    This section reuses the generic program and symbolic Hoare proof above.
    Only the concrete assignments and the analytical value of the successful
    path change.  The motivating example calls this probability [r_2]. *)

Definition run_11 (epsilon : R) : Cmd :=
  <{ q1 := 1; q2 := 1; $(two_queries epsilon) }>.

Definition path_integral_11 (epsilon : R) : PConstruct :=
  [[
    integral threshold ~ $(threshold_distribution epsilon),
    integral noisy1 ~ laplace ( 1, $((4 / epsilon)%R) ),
    integral noisy2 ~ laplace ( 1, $((4 / epsilon)%R) ),
    indicator[$(path_event)]
  ]].

(** This is exactly the expression [r_2(epsilon)] printed in the motivating
    example. *)
Definition closed_form_probability_11 (epsilon : R) : R :=
  (-22 + 32 * exp (epsilon / 4) - 3 * epsilon) /
  (48 * exp (epsilon / 2)).

Definition nested_integral_11 (epsilon : R) : R :=
  real_integral
    (fun threshold =>
      laplace_density_R 0 (2 / epsilon) threshold *
      real_integral
        (fun noisy1 =>
          laplace_density_R 1 (4 / epsilon) noisy1 *
          real_integral
            (fun noisy2 =>
              laplace_density_R 1 (4 / epsilon) noisy2 *
              real_indicator
                (noisy1 < threshold /\ threshold <= noisy2)%R))).

Definition threshold_integrand_11 (epsilon threshold : R) : R :=
  laplace_density_R 0 (2 / epsilon) threshold *
  laplace_cdf 1 (4 / epsilon) threshold *
  (1 - laplace_cdf 1 (4 / epsilon) threshold).

Lemma nested_integral_11_reduce :
  forall epsilon : R,
    (0 < epsilon)%R ->
    nested_integral_11 epsilon =
      real_integral (threshold_integrand_11 epsilon).
Proof.
  intros epsilon Hepsilon.
  unfold nested_integral_11, threshold_integrand_11.
  apply real_integral_extensional.
  intro threshold.
  assert (Hinner :
    forall noisy1 : R,
      real_integral
        (fun noisy2 =>
          laplace_density_R 1 (4 / epsilon) noisy2 *
          real_indicator
            (noisy1 < threshold /\ threshold <= noisy2)%R) =
      (real_indicator (noisy1 < threshold)%R *
        (1 - laplace_cdf 1 (4 / epsilon) threshold))%R).
  {
    intro noisy1.
    destruct (Rlt_dec noisy1 threshold) as [Hlt | Hnlt].
    - rewrite (real_indicator_true _ Hlt).
      transitivity
        (real_integral
          (fun noisy2 =>
            laplace_density_R 1 (4 / epsilon) noisy2 *
            real_indicator (threshold <= noisy2)%R)).
      + apply real_integral_extensional.
        intro noisy2.
        destruct (Rle_dec threshold noisy2) as [Hle | Hnle].
        * rewrite (real_indicator_true _ (conj Hlt Hle)).
          rewrite (real_indicator_true _ Hle).
          reflexivity.
        * rewrite (real_indicator_false
            (noisy1 < threshold /\ threshold <= noisy2)%R) by tauto.
          rewrite (real_indicator_false (threshold <= noisy2)%R) by exact Hnle.
          ring.
      + unfold laplace_density_R.
        rewrite (laplace_integral_survival 1 (4 / epsilon) threshold
          (query_scale_positive epsilon Hepsilon)).
        ring.
    - rewrite (real_indicator_false (noisy1 < threshold)%R) by exact Hnlt.
      transitivity (real_integral (fun _ : R => 0%R)).
      + apply real_integral_extensional.
        intro noisy2.
        rewrite (real_indicator_false
          (noisy1 < threshold /\ threshold <= noisy2)%R) by tauto.
        ring.
      + rewrite real_integral_zero; ring.
  }
  assert (Hnoisy1 :
    real_integral
      (fun noisy1 =>
        laplace_density_R 1 (4 / epsilon) noisy1 *
        real_integral
          (fun noisy2 =>
            laplace_density_R 1 (4 / epsilon) noisy2 *
            real_indicator
              (noisy1 < threshold /\ threshold <= noisy2)%R)) =
    (laplace_cdf 1 (4 / epsilon) threshold *
      (1 - laplace_cdf 1 (4 / epsilon) threshold))%R).
  {
    transitivity
      (real_integral
        (fun noisy1 =>
          laplace_density_R 1 (4 / epsilon) noisy1 *
          (real_indicator (noisy1 < threshold)%R *
            (1 - laplace_cdf 1 (4 / epsilon) threshold)))).
    - apply real_integral_extensional.
      intro noisy1.
      rewrite Hinner.
      reflexivity.
    - transitivity
        ((real_integral
          (fun noisy1 =>
            laplace_density_R 1 (4 / epsilon) noisy1 *
            real_indicator (noisy1 < threshold)%R)) *
          (1 - laplace_cdf 1 (4 / epsilon) threshold))%R.
      + rewrite <- real_integral_scale_right.
        apply real_integral_extensional.
        intro noisy1.
        ring.
      + unfold laplace_density_R.
        rewrite (laplace_integral_strict_cdf 1 (4 / epsilon) threshold
          (query_scale_positive epsilon Hepsilon)).
        ring.
  }
  rewrite Hnoisy1.
  ring.
Qed.

Definition threshold_integrand_rate_11 (rate threshold : R) : R :=
  rate * exp (- 2 * rate * Rabs threshold) *
  laplace_cdf_rate 1 rate threshold *
  (1 - laplace_cdf_rate 1 rate threshold).

Lemma threshold_integrand_11_as_rate :
  forall (epsilon threshold : R),
    epsilon <> 0%R ->
    threshold_integrand_11 epsilon threshold =
      threshold_integrand_rate_11 (epsilon / 4) threshold.
Proof.
  intros epsilon threshold Hepsilon.
  unfold threshold_integrand_11, threshold_integrand_rate_11,
    laplace_density_R.
  repeat rewrite
    (laplace_cdf_scale_as_rate epsilon 1 threshold Hepsilon).
  assert (Hcoefficient :
    ((1 / (2 * (2 / epsilon))) = epsilon / 4)%R).
  { field; exact Hepsilon. }
  assert (Hexponent :
    ((- Rabs (threshold - 0) / (2 / epsilon)) =
      (- 2 * (epsilon / 4) * Rabs threshold))%R).
  {
    rewrite Rminus_0_r.
    field; exact Hepsilon.
  }
  rewrite Hcoefficient, Hexponent.
  ring.
Qed.

Lemma integrand_rate_11_below_pointwise :
  forall rate threshold : R,
    (threshold < 0)%R ->
    threshold_integrand_rate_11 rate threshold =
      (((rate / 2) * exp (- rate)) *
          exp ((3 * rate) * threshold) +
       (- rate / 4 * exp (- 2 * rate)) *
          exp ((4 * rate) * threshold))%R.
Proof.
  intros rate threshold Hthreshold.
  unfold threshold_integrand_rate_11.
  rewrite (Rabs_left threshold Hthreshold).
  repeat rewrite (laplace_cdf_rate_left 1 rate threshold) by lra.
  assert (Hexp3 :
    (exp (- 2 * rate * - threshold) *
      exp (rate * (threshold - 1)) =
      exp (- rate) * exp ((3 * rate) * threshold))%R).
  {
    rewrite <- exp_plus, <- exp_plus.
    f_equal; ring.
  }
  assert (Hexp4 :
    (exp (- 2 * rate * - threshold) *
      exp (rate * (threshold - 1)) *
      exp (rate * (threshold - 1)) =
      exp (- 2 * rate) * exp ((4 * rate) * threshold))%R).
  {
    rewrite <- exp_plus, <- exp_plus, <- exp_plus.
    f_equal; ring.
  }
  transitivity
    (((rate / 2) *
        (exp (- 2 * rate * - threshold) *
          exp (rate * (threshold - 1)))) +
      (- rate / 4) *
        (exp (- 2 * rate * - threshold) *
          exp (rate * (threshold - 1)) *
          exp (rate * (threshold - 1))))%R.
  - field.
  - rewrite Hexp4, Hexp3.
    field.
Qed.

Lemma integrand_rate_11_between_pointwise :
  forall rate threshold : R,
    (0 <= threshold < 1)%R ->
    threshold_integrand_rate_11 rate threshold =
      (((rate / 2) * exp (- rate)) *
          exp ((- rate) * threshold) +
       (- rate / 4) * exp (- 2 * rate))%R.
Proof.
  intros rate threshold Hthreshold.
  unfold threshold_integrand_rate_11.
  rewrite (Rabs_right threshold) by lra.
  repeat rewrite (laplace_cdf_rate_left 1 rate threshold) by lra.
  assert (Hexp1 :
    (exp (- 2 * rate * threshold) *
      exp (rate * (threshold - 1)) =
      exp (- rate) * exp ((- rate) * threshold))%R).
  {
    rewrite <- exp_plus, <- exp_plus.
    f_equal; ring.
  }
  assert (Hexp0 :
    (exp (- 2 * rate * threshold) *
      exp (rate * (threshold - 1)) *
      exp (rate * (threshold - 1)) =
      exp (- 2 * rate))%R).
  {
    rewrite <- exp_plus, <- exp_plus.
    f_equal; ring.
  }
  transitivity
    (((rate / 2) *
        (exp (- 2 * rate * threshold) *
          exp (rate * (threshold - 1)))) +
      (- rate / 4) *
        (exp (- 2 * rate * threshold) *
          exp (rate * (threshold - 1)) *
          exp (rate * (threshold - 1))))%R.
  - field.
  - rewrite Hexp0, Hexp1.
    field.
Qed.

Lemma integrand_rate_11_above_pointwise :
  forall rate threshold : R,
    (1 <= threshold)%R ->
    threshold_integrand_rate_11 rate threshold =
      (((rate / 2) * exp rate) *
          exp ((- 3 * rate) * threshold) +
       (- rate / 4 * exp (2 * rate)) *
          exp ((- 4 * rate) * threshold))%R.
Proof.
  intros rate threshold Hthreshold.
  unfold threshold_integrand_rate_11.
  rewrite (Rabs_right threshold) by lra.
  repeat rewrite (laplace_cdf_rate_right 1 rate threshold) by lra.
  assert (Hexp3 :
    (exp (- 2 * rate * threshold) *
      exp (- rate * (threshold - 1)) =
      exp rate * exp ((- 3 * rate) * threshold))%R).
  {
    rewrite <- exp_plus, <- exp_plus.
    f_equal; ring.
  }
  assert (Hexp4 :
    (exp (- 2 * rate * threshold) *
      exp (- rate * (threshold - 1)) *
      exp (- rate * (threshold - 1)) =
      exp (2 * rate) * exp ((- 4 * rate) * threshold))%R).
  {
    rewrite <- exp_plus, <- exp_plus, <- exp_plus.
    f_equal; ring.
  }
  transitivity
    (((rate / 2) *
        (exp (- 2 * rate * threshold) *
          exp (- rate * (threshold - 1)))) +
      (- rate / 4) *
        (exp (- 2 * rate * threshold) *
          exp (- rate * (threshold - 1)) *
          exp (- rate * (threshold - 1))))%R.
  - field.
  - rewrite Hexp4, Hexp3.
    field.
Qed.

Lemma integral_rate_11_below :
  forall rate : R,
    (0 < rate)%R ->
    real_integral_below 0 (threshold_integrand_rate_11 rate) =
      (exp (- rate) / 6 - exp (- 2 * rate) / 16)%R.
Proof.
  intros rate Hrate.
  transitivity
    (real_integral_below 0
      (fun threshold =>
        ((rate / 2) * exp (- rate)) *
          exp ((3 * rate) * threshold) +
        (- rate / 4 * exp (- 2 * rate)) *
          exp ((4 * rate) * threshold))).
  - unfold real_integral_below.
    apply real_integral_extensional.
    intro threshold.
    destruct (Rlt_dec threshold 0) as [Hthreshold | Hthreshold].
    + rewrite (real_indicator_true _ Hthreshold).
      rewrite (integrand_rate_11_below_pointwise
        rate threshold Hthreshold).
      reflexivity.
    + rewrite (real_indicator_false (threshold < 0)%R) by exact Hthreshold.
      ring.
  - rewrite real_integral_below_add.
    rewrite !real_integral_below_scale.
    rewrite (real_integral_exp_below 0 (3 * rate)) by lra.
    rewrite (real_integral_exp_below 0 (4 * rate)) by lra.
    rewrite !Rmult_0_r, !exp_0.
    field; lra.
Qed.

Lemma integral_rate_11_between :
  forall rate : R,
    (0 < rate)%R ->
    real_integral_between 0 1 (threshold_integrand_rate_11 rate) =
      (exp (- rate) / 2 - exp (- 2 * rate) / 2 -
        rate * exp (- 2 * rate) / 4)%R.
Proof.
  intros rate Hrate.
  transitivity
    (real_integral_between 0 1
      (fun threshold =>
        ((rate / 2) * exp (- rate)) *
          exp ((- rate) * threshold) +
        (- rate / 4) * exp (- 2 * rate))).
  - unfold real_integral_between.
    apply real_integral_extensional.
    intro threshold.
    destruct (excluded_middle_informative (0 <= threshold < 1)%R)
      as [Hthreshold | Hthreshold].
    + rewrite (real_indicator_true _ Hthreshold).
      rewrite (integrand_rate_11_between_pointwise
        rate threshold Hthreshold).
      reflexivity.
    + rewrite (real_indicator_false (0 <= threshold < 1)%R) by
        exact Hthreshold.
      ring.
  - rewrite real_integral_between_add.
    rewrite real_integral_between_scale.
    rewrite (real_integral_exp_between 0 1 (- rate)) by lra.
    rewrite (real_integral_between_constant 0 1
      ((- rate / 4) * exp (- 2 * rate))) by lra.
    rewrite !Rmult_0_r, !Rmult_1_r, !exp_0.
    assert (Hexp2 :
      (exp (- rate) * exp (- rate) = exp (- 2 * rate))%R).
    {
      rewrite <- exp_plus.
      f_equal; ring.
    }
    rewrite <- Hexp2.
    field; lra.
Qed.

Lemma integral_rate_11_above :
  forall rate : R,
    (0 < rate)%R ->
    real_integral_above 1 (threshold_integrand_rate_11 rate) =
      (exp (- 2 * rate) / 6 - exp (- 2 * rate) / 16)%R.
Proof.
  intros rate Hrate.
  transitivity
    (real_integral_above 1
      (fun threshold =>
        ((rate / 2) * exp rate) *
          exp ((- 3 * rate) * threshold) +
        (- rate / 4 * exp (2 * rate)) *
          exp ((- 4 * rate) * threshold))).
  - unfold real_integral_above.
    apply real_integral_extensional.
    intro threshold.
    destruct (Rle_dec 1 threshold) as [Hthreshold | Hthreshold].
    + rewrite (real_indicator_true _ Hthreshold).
      rewrite (integrand_rate_11_above_pointwise
        rate threshold Hthreshold).
      reflexivity.
    + rewrite (real_indicator_false (1 <= threshold)%R) by exact Hthreshold.
      ring.
  - rewrite real_integral_above_add.
    rewrite !real_integral_above_scale.
    rewrite (real_integral_exp_above 1 (- 3 * rate)) by lra.
    rewrite (real_integral_exp_above 1 (- 4 * rate)) by lra.
    rewrite !Rmult_1_r.
    assert (Hexp2_left :
      (exp rate * exp (- 3 * rate) = exp (- 2 * rate))%R).
    {
      rewrite <- exp_plus.
      f_equal; ring.
    }
    assert (Hexp2_right :
      (exp (2 * rate) * exp (- 4 * rate) = exp (- 2 * rate))%R).
    {
      rewrite <- exp_plus.
      f_equal; ring.
    }
    transitivity
      ((exp rate * exp (- 3 * rate)) / 6 -
        (exp (2 * rate) * exp (- 4 * rate)) / 16)%R.
    + field; lra.
    + rewrite Hexp2_left, Hexp2_right.
      reflexivity.
Qed.

Lemma threshold_integral_rate_11 :
  forall rate : R,
    (0 < rate)%R ->
    real_integral (threshold_integrand_rate_11 rate) =
      ((32 * exp (- rate) - 22 * exp (- 2 * rate) -
        12 * rate * exp (- 2 * rate)) / 48)%R.
Proof.
  intros rate Hrate.
  rewrite (real_integral_split_three
    (threshold_integrand_rate_11 rate) 0 1) by lra.
  rewrite (integral_rate_11_below rate Hrate).
  rewrite (integral_rate_11_between rate Hrate).
  rewrite (integral_rate_11_above rate Hrate).
  field.
Qed.

Lemma rate_form_equals_closed_form_11 :
  forall epsilon : R,
    ((32 * exp (- (epsilon / 4)) -
       22 * exp (- 2 * (epsilon / 4)) -
       12 * (epsilon / 4) * exp (- 2 * (epsilon / 4))) / 48)%R =
      closed_form_probability_11 epsilon.
Proof.
  intro epsilon.
  unfold closed_form_probability_11.
  assert (Hexp_nonzero : exp (epsilon / 2) <> 0%R).
  { apply exp_neq_0. }
  assert (Hexp1 :
    (exp (- (epsilon / 4)) * exp (epsilon / 2) =
      exp (epsilon / 4))%R).
  {
    rewrite <- exp_plus.
    f_equal; field.
  }
  assert (Hexp2 :
    (exp (- 2 * (epsilon / 4)) * exp (epsilon / 2) = 1)%R).
  {
    rewrite <- exp_plus.
    replace (- 2 * (epsilon / 4) + epsilon / 2)%R with 0%R by field.
    apply exp_0.
  }
  assert (Hnumerator :
    (-22 + 32 * exp (epsilon / 4) - 3 * epsilon =
      exp (epsilon / 2) *
        (32 * exp (- (epsilon / 4)) -
         22 * exp (- 2 * (epsilon / 4)) -
         12 * (epsilon / 4) * exp (- 2 * (epsilon / 4))))%R).
  {
    transitivity
      (-22 * (exp (- 2 * (epsilon / 4)) * exp (epsilon / 2)) +
       32 * (exp (- (epsilon / 4)) * exp (epsilon / 2)) -
       12 * (epsilon / 4) *
         (exp (- 2 * (epsilon / 4)) * exp (epsilon / 2)))%R.
    - rewrite Hexp1, Hexp2.
      field.
    - field.
  }
  rewrite Hnumerator.
  field; exact Hexp_nonzero.
Qed.

Theorem nested_integral_value_11 :
  forall epsilon : R,
    (0 < epsilon)%R ->
    nested_integral_11 epsilon = closed_form_probability_11 epsilon.
Proof.
  intros epsilon Hepsilon.
  rewrite (nested_integral_11_reduce epsilon Hepsilon).
  transitivity
    (real_integral
      (threshold_integrand_rate_11 (epsilon / 4))).
  - apply real_integral_extensional.
    intro threshold.
    apply threshold_integrand_11_as_rate.
    lra.
  - rewrite (threshold_integral_rate_11 (epsilon / 4)) by lra.
    apply rate_form_equals_closed_form_11.
Qed.

Lemma path_integral_11_eval :
  forall (epsilon : R) (v : state),
    q_eval (path_integral_11 epsilon) v = nested_integral_11 epsilon.
Proof.
  intros epsilon v.
  unfold path_integral_11, nested_integral_11,
    laplace_density_R, threshold_distribution,
    query_distribution, path_event, c_and, c_not, c_lt.
  cbn [q_eval distribution_density term_eval satisfies update_real
    real_program_values].
  apply real_integral_extensional.
  intro threshold.
  f_equal.
  apply real_integral_extensional.
  intro noisy1.
  f_equal.
  apply real_integral_extensional.
  intro noisy2.
  f_equal.
  apply real_indicator_extensional.
  unfold SVT_notation.threshold, SVT_notation.noisy1,
    SVT_notation.noisy2.
  cbn [satisfies c_not term_eval update_real update_real_values
    real_program_values real_program_var_eq_dec].
  change
    (((((threshold <= noisy1)%R -> False) ->
        (threshold <= noisy2)%R -> False) -> False) <->
      ((noisy1 < threshold)%R /\ (threshold <= noisy2)%R)).
  split.
  - intro H.
    split; lra.
  - intros [Hlt Hle] Hnot.
    apply Hnot; [lra | exact Hle].
Qed.

Definition symbolic_concrete_pre_11 (epsilon p : R) : PFormula :=
  subst_real_pformula q1 <{ 1 }>
    (subst_real_pformula q2 <{ 1 }>
      (symbolic_pre epsilon p)).

Theorem symbolic_concrete_hoare_11 :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(symbolic_concrete_pre_11 epsilon p) }}
      $(run_11 epsilon)
    {{ $(bot_top_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold run_11, symbolic_concrete_pre_11.
  eapply HSeq with
    (eta2 := subst_real_pformula q2 <{ 1 }>
      (symbolic_pre epsilon p)).
  - apply HRealAssign.
  - eapply HSeq with (eta2 := symbolic_pre epsilon p).
    + apply HRealAssign.
    + apply symbolic_hoare.
      exact Hepsilon.
Qed.

Lemma path_substitution_11 :
  forall epsilon : R,
    subst_real_pconstruct q1 <{ 1 }>
      (subst_real_pconstruct q2 <{ 1 }>
        (path_integral epsilon)) =
      path_integral_11 epsilon.
Proof.
  intro epsilon.
  unfold path_integral, path_integral_11,
    threshold_distribution, query_distribution,
    q1, q2, threshold, noisy1, noisy2.
  cbn [subst_real_pconstruct subst_real_pconstruct_fuel
    subst_real_distribution subst_real_term subst_real_cformula
    pconstruct_size pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars
    cformula_real_program_vars List.in_dec real_program_var_eq_dec].
  reflexivity.
Qed.

Lemma symbolic_concrete_pre_11_shape :
  forall epsilon p : R,
    symbolic_concrete_pre_11 epsilon p =
      [[ $(normalized) /\
         E[$(subst_real_pconstruct q1 <{ 1 }>
           (subst_real_pconstruct q2 <{ 1 }>
             (path_integral epsilon)))] = $(p) ]].
Proof.
  intros epsilon p.
  unfold symbolic_concrete_pre_11, symbolic_pre, normalized.
  cbn [subst_real_pformula subst_real_pterm].
  reflexivity.
Qed.

Lemma normalized_implies_concrete_pre_11 :
  forall epsilon : R,
    (0 < epsilon)%R ->
    pformula_valid
      [[ $(normalized) ->
         $(symbolic_concrete_pre_11 epsilon
           (closed_form_probability_11 epsilon)) ]].
Proof.
  intros epsilon Hepsilon.
  unfold pformula_valid.
  intro ps.
  rewrite symbolic_concrete_pre_11_shape.
  rewrite path_substitution_11.
  assert (Hpath :
    expectation (pstate_measure ps)
      (q_eval (path_integral_11 epsilon)) =
    (closed_form_probability_11 epsilon *
      expectation (pstate_measure ps) (q_eval [[ indicator[true] ]]))%R).
  {
    transitivity
      (expectation (pstate_measure ps)
        (fun _ : state => closed_form_probability_11 epsilon)).
    - apply expectation_extensional.
      intro v.
      rewrite path_integral_11_eval.
      apply nested_integral_value_11.
      exact Hepsilon.
    - apply expectation_constant.
  }
  unfold normalized.
  cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
  intro Hnormalized.
  assert (Hmass_upper :
    (expectation (pstate_measure ps) (q_eval [[ indicator[true] ]]) <= 1)%R).
  {
    apply NNPP; intro Hnot.
    apply Hnormalized.
    intro Hupper; contradiction.
  }
  assert (Hmass_lower :
    (1 <= expectation (pstate_measure ps) (q_eval [[ indicator[true] ]]))%R).
  {
    apply NNPP; intro Hnot.
    apply Hnormalized.
    intros Hupper Hlower; contradiction.
  }
  assert (Hmass :
    expectation (pstate_measure ps) (q_eval [[ indicator[true] ]]) = 1%R)
    by lra.
  assert (Hpath_value :
    expectation (pstate_measure ps) (q_eval (path_integral_11 epsilon)) =
      closed_form_probability_11 epsilon).
  {
    rewrite Hpath, Hmass; ring.
  }
  assert (Hpath_upper :
    (expectation (pstate_measure ps)
      (q_eval (path_integral_11 epsilon)) <=
        closed_form_probability_11 epsilon)%R)
    by lra.
  assert (Hpath_lower :
    (closed_form_probability_11 epsilon <=
      expectation (pstate_measure ps)
        (q_eval (path_integral_11 epsilon)))%R)
    by lra.
  tauto.
Qed.

Theorem run_11_bot_top_probability :
  forall epsilon : R,
    (0 < epsilon)%R ->
    {{ $(normalized) }}
      $(run_11 epsilon)
    {{ $(bot_top_probability (closed_form_probability_11 epsilon)) }}.
Proof.
  intros epsilon Hepsilon.
  eapply HConseq with
    (eta1 := symbolic_concrete_pre_11 epsilon
      (closed_form_probability_11 epsilon))
    (eta2 := bot_top_probability (closed_form_probability_11 epsilon)).
  - apply normalized_implies_concrete_pre_11.
    exact Hepsilon.
  - apply symbolic_concrete_hoare_11.
    exact Hepsilon.
  - unfold pformula_valid.
    intro ps; cbn [psatisfies]; tauto.
Qed.
