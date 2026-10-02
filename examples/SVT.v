(**
  The two-query Sparse Vector Technique instance from the motivating example
  of "Deciding Differential Privacy for Programs with Finite Inputs and
  Outputs".

      out1 := ff;  out2 := ff;
      threshold <- sample(Laplace(0,  2/epsilon));
      noisy1    <- sample(Laplace(q1, 4/epsilon));
      above1    := (threshold <= noisy1);
      if above1 then out1 := tt
      else
        noisy2 <- sample(Laplace(q2, 4/epsilon));
        above2 := (threshold <= noisy2);
        if above2 then out2 := tt else skip end
      end

  THE MAIN TRIPLE ([svt_01_bot_top_probability], for [0 < epsilon]).  The
  concrete run [svt_01] prefixes [q1 := 0; q2 := 1]:

      { Pr[tt] = 1 }
          svt_01 epsilon
      { Pr[~out1 /\ out2] = r1(epsilon) }

      r1(epsilon) = (24 e^(3eps/4) - 1 + 8 e^(eps/4) - 21 e^(eps/2))
                    / (48 e^(3eps/4))

  So: given that the initial measure is a probability measure (total mass
  1), the program answers (bot, top) -- first query below threshold, second
  above -- with exactly probability [r1].  The precondition is the whole of
  the assumption: no other property of the starting state is used.

  TWO MORE GENERAL TRIPLES, of which the above is the instance obtained by
  discharging the precondition from [normalized]:

      [svt_symbolic_hoare]           { svt_symbolic_pre epsilon p }
                                         svt_two_queries epsilon
                                     { Pr[~out1 /\ out2] = p }

      [svt_symbolic_concrete_hoare]  { svt_symbolic_concrete_pre epsilon p }
                                         svt_01 epsilon
                                     { Pr[~out1 /\ out2] = p }

  The paper writes [Lap(rate, location)], whereas [CPHL.Laplace] stores
  [(location, scale)].  Consequently the rates [epsilon/2] and [epsilon/4]
  below become the scales [2/epsilon] and [4/epsilon].

  The paper also prints a plus sign before the [21 exp(epsilon/2)] term of
  [r1]; that expression exceeds one for small positive epsilon.  Direct
  integration gives the minus sign used here.  See [svt_r1].
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
Definition svt_q1 : RealProgramVar := real_program_var "svt_q1".
Definition svt_q2 : RealProgramVar := real_program_var "svt_q2".
Definition svt_threshold : RealProgramVar := real_program_var "svt_threshold".
Definition svt_noisy1 : RealProgramVar := real_program_var "svt_noisy1".
Definition svt_noisy2 : RealProgramVar := real_program_var "svt_noisy2".

Definition svt_above1 : BoolProgramVar := bool_program_var "svt_above1".
Definition svt_above2 : BoolProgramVar := bool_program_var "svt_above2".
Definition svt_out1 : BoolProgramVar := bool_program_var "svt_out1".
Definition svt_out2 : BoolProgramVar := bool_program_var "svt_out2".

(** Rigid variables used only inside the derived conditional proof. *)
Definition svt_y_then : ProbLogicVar := prob_logic_var "svt_y_then".
Definition svt_y_else : ProbLogicVar := prob_logic_var "svt_y_else".

Definition svt_threshold_distribution (epsilon : R) : Distribution :=
  <{ laplace ( 0, $((2 / epsilon)%R) ) }>.

Definition svt_query_distribution
  (epsilon : R) (query : RealProgramVar) : Distribution :=
  <{ laplace ( query, $((4 / epsilon)%R) ) }>.

Definition svt_first_comparison : CFormula :=
  <{ svt_threshold <= svt_noisy1 }>.

Definition svt_second_comparison : CFormula :=
  <{ svt_threshold <= svt_noisy2 }>.

(** The second unfolded iteration is executed only after the first answer was
    [bot]. *)
Definition svt_second_iteration (epsilon : R) : Cmd :=
  <{
    svt_noisy2 sample $(svt_query_distribution epsilon svt_q2);
    svt_above2 b= $(svt_second_comparison);
    if svt_above2 then svt_out2 b= true else skip end
  }>.

(** The generic [N = 2], [c = 1] SVT command.  The output initialization is
    explicit, and the true branch of the first comparison implements the
    early exit. *)
Definition svt_two_queries (epsilon : R) : Cmd :=
  <{
    svt_out1 b= false;
    svt_out2 b= false;
    svt_threshold sample $(svt_threshold_distribution epsilon);
    svt_noisy1 sample $(svt_query_distribution epsilon svt_q1);
    svt_above1 b= $(svt_first_comparison);
    if svt_above1 then svt_out1 b= true
    else $(svt_second_iteration epsilon)
    end
  }>.

(** A concrete run on the input vector [[0, 1]]. *)
Definition svt_01 (epsilon : R) : Cmd :=
  <{ svt_q1 := 0; svt_q2 := 1; $(svt_two_queries epsilon) }>.

Definition svt_bot_top : CFormula :=
  <{ ~ svt_out1 /\ svt_out2 }>.

Definition svt_path_event : CFormula :=
  <{ svt_noisy1 < svt_threshold /\ svt_threshold <= svt_noisy2 }>.

Definition svt_path_construct (epsilon : R) : PConstruct :=
  [[
    integral svt_threshold ~ $(svt_threshold_distribution epsilon),
    integral svt_noisy1 ~ $(svt_query_distribution epsilon svt_q1),
    integral svt_noisy2 ~ $(svt_query_distribution epsilon svt_q2),
    indicator[$(svt_path_event)]
  ]].

Definition svt_path_construct_01 (epsilon : R) : PConstruct :=
  [[
    integral svt_threshold ~ $(svt_threshold_distribution epsilon),
    integral svt_noisy1 ~ laplace ( 0, $((4 / epsilon)%R) ),
    integral svt_noisy2 ~ laplace ( 1, $((4 / epsilon)%R) ),
    indicator[$(svt_path_event)]
  ]].

Definition probability_of_bot_top_equals (r : R) : PFormula :=
  [[ Pr[$(svt_bot_top)] = $(r) ]].

Definition normalized : PFormula :=
  [[ Pr[true] = 1 ]].

(** The paper prints a plus sign before the [21 exp(epsilon/2)] term.  That
    expression exceeds one for small positive epsilon.  Direct integration
    gives the corrected minus sign below. *)
Definition svt_r1 (epsilon : R) : R :=
  (24 * exp (3 * epsilon / 4) - 1 + 8 * exp (epsilon / 4) -
    21 * exp (epsilon / 2)) /
  (48 * exp (3 * epsilon / 4)).

Lemma svt_threshold_scale_positive :
  forall epsilon : R, (0 < epsilon)%R -> (0 < 2 / epsilon)%R.
Proof.
  intros epsilon Hepsilon.
  unfold Rdiv.
  apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; exact Hepsilon].
Qed.

Lemma svt_query_scale_positive :
  forall epsilon : R, (0 < epsilon)%R -> (0 < 4 / epsilon)%R.
Proof.
  intros epsilon Hepsilon.
  unfold Rdiv.
  apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; exact Hepsilon].
Qed.

(** Raw analytical presentation of the nested probability construct. *)
Definition laplace_density_R (location scale z : R) : R :=
  (1 / (2 * scale)) * exp (- Rabs (z - location) / scale).

Definition svt_nested_integral (epsilon : R) : R :=
  real_integral
    (fun svt_threshold =>
      laplace_density_R 0 (2 / epsilon) svt_threshold *
      real_integral
        (fun svt_noisy1 =>
          laplace_density_R 0 (4 / epsilon) svt_noisy1 *
          real_integral
            (fun svt_noisy2 =>
              laplace_density_R 1 (4 / epsilon) svt_noisy2 *
              real_indicator
                (svt_noisy1 < svt_threshold /\ svt_threshold <= svt_noisy2)%R))).

Definition svt_threshold_integrand (epsilon svt_threshold : R) : R :=
  laplace_density_R 0 (2 / epsilon) svt_threshold *
  laplace_cdf 0 (4 / epsilon) svt_threshold *
  (1 - laplace_cdf 1 (4 / epsilon) svt_threshold).

Lemma svt_nested_integral_reduce :
  forall epsilon : R,
    (0 < epsilon)%R ->
    svt_nested_integral epsilon =
      real_integral (svt_threshold_integrand epsilon).
Proof.
  intros epsilon Hepsilon.
  unfold svt_nested_integral, svt_threshold_integrand.
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
          (svt_query_scale_positive epsilon Hepsilon)).
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
          (svt_query_scale_positive epsilon Hepsilon)).
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

Definition svt_threshold_integrand_rate (rate svt_threshold : R) : R :=
  rate * exp (- 2 * rate * Rabs svt_threshold) *
  laplace_cdf_rate 0 rate svt_threshold *
  (1 - laplace_cdf_rate 1 rate svt_threshold).

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

Lemma svt_threshold_integrand_as_rate :
  forall (epsilon svt_threshold : R),
    epsilon <> 0%R ->
    svt_threshold_integrand epsilon svt_threshold =
      svt_threshold_integrand_rate (epsilon / 4) svt_threshold.
Proof.
  intros epsilon threshold Hepsilon.
  unfold svt_threshold_integrand, svt_threshold_integrand_rate,
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

Lemma svt_integrand_rate_below_pointwise :
  forall rate svt_threshold : R,
    (svt_threshold < 0)%R ->
    svt_threshold_integrand_rate rate svt_threshold =
      ((rate / 2) * exp ((3 * rate) * svt_threshold) +
       (- rate / 4 * exp (- rate)) * exp ((4 * rate) * svt_threshold))%R.
Proof.
  intros rate threshold Hthreshold.
  unfold svt_threshold_integrand_rate.
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

Lemma svt_integrand_rate_between_pointwise :
  forall rate svt_threshold : R,
    (0 <= svt_threshold < 1)%R ->
    svt_threshold_integrand_rate rate svt_threshold =
      ((rate * (1 + exp (- rate) / 4)) *
          exp ((- 2 * rate) * svt_threshold) +
       (- rate / 2) * exp ((- 3 * rate) * svt_threshold) +
       (- rate / 2 * exp (- rate)) *
          exp ((- rate) * svt_threshold))%R.
Proof.
  intros rate threshold Hthreshold.
  unfold svt_threshold_integrand_rate.
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

Lemma svt_integrand_rate_above_pointwise :
  forall rate svt_threshold : R,
    (1 <= svt_threshold)%R ->
    svt_threshold_integrand_rate rate svt_threshold =
      ((rate / 2 * exp rate) * exp ((- 3 * rate) * svt_threshold) +
       (- rate / 4 * exp rate) * exp ((- 4 * rate) * svt_threshold))%R.
Proof.
  intros rate threshold Hthreshold.
  unfold svt_threshold_integrand_rate.
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

Lemma svt_integral_rate_below :
  forall rate : R,
    (0 < rate)%R ->
    real_integral_below 0 (svt_threshold_integrand_rate rate) =
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
      rewrite (svt_integrand_rate_below_pointwise rate threshold Hthreshold).
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

Lemma svt_integral_rate_between :
  forall rate : R,
    (0 < rate)%R ->
    real_integral_between 0 1 (svt_threshold_integrand_rate rate) =
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
      rewrite (svt_integrand_rate_between_pointwise rate threshold Hthreshold).
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

Lemma svt_integral_rate_above :
  forall rate : R,
    (0 < rate)%R ->
    real_integral_above 1 (svt_threshold_integrand_rate rate) =
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
      rewrite (svt_integrand_rate_above_pointwise rate threshold Hthreshold).
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

Lemma svt_threshold_integral_rate :
  forall rate : R,
    (0 < rate)%R ->
    real_integral (svt_threshold_integrand_rate rate) =
      ((24 - 21 * exp (- rate) + 8 * exp (- 2 * rate) -
        exp (- 3 * rate)) / 48)%R.
Proof.
  intros rate Hrate.
  rewrite (real_integral_split_three
    (svt_threshold_integrand_rate rate) 0 1) by lra.
  rewrite (svt_integral_rate_below rate Hrate).
  rewrite (svt_integral_rate_between rate Hrate).
  rewrite (svt_integral_rate_above rate Hrate).
  field.
Qed.

Lemma svt_rate_form_equals_r1 :
  forall epsilon : R,
    epsilon <> 0%R ->
    ((24 - 21 * exp (- (epsilon / 4)) +
       8 * exp (- 2 * (epsilon / 4)) -
       exp (- 3 * (epsilon / 4))) / 48)%R =
      svt_r1 epsilon.
Proof.
  intros epsilon Hepsilon.
  unfold svt_r1.
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

Theorem svt_nested_integral_value :
  forall epsilon : R,
    (0 < epsilon)%R ->
    svt_nested_integral epsilon = svt_r1 epsilon.
Proof.
  intros epsilon Hepsilon.
  rewrite (svt_nested_integral_reduce epsilon Hepsilon).
  transitivity
    (real_integral
      (svt_threshold_integrand_rate (epsilon / 4))).
  - apply real_integral_extensional.
    intro threshold.
    apply svt_threshold_integrand_as_rate.
    lra.
  - rewrite (svt_threshold_integral_rate (epsilon / 4)) by lra.
    apply svt_rate_form_equals_r1.
    lra.
Qed.

(** Hoare-logic plumbing.  These abbreviations keep the weakest
    preconditions generated by the unfolded conditionals readable. *)
Definition svt_event_probability (r : R) (gamma : CFormula) : PFormula :=
  [[ $(r) = Pr[$(gamma)] ]].

Definition svt_rigid_constant
  (y : ProbLogicVar) (r : R) : PFormula :=
  [[ y = $(r) ]].

Lemma svt_rigid_constant_analytical :
  forall (y : ProbLogicVar) (r : R),
    pformula_analytical (svt_rigid_constant y r).
Proof.
  intros y r.
  cbn [svt_rigid_constant p_eq p_and p_not
    pformula_analytical pterm_analytical].
  tauto.
Qed.

Lemma svt_add_rigid_constant :
  forall (eta : PFormula) (s : Cmd) (gamma : CFormula)
    (y : ProbLogicVar) (r : R),
    {{ $(eta) }} $(s) {{ $(svt_event_probability r gamma) }} ->
    {{ $(eta) /\ $(svt_rigid_constant y r) }} $(s)
      {{ y = Pr[$(gamma)] }}.
Proof.
  intros eta s gamma y r Hbranch.
  assert (Hevent :
    hoare_derivable (p_and eta (svt_rigid_constant y r)) s
      (svt_event_probability r gamma)).
  {
    eapply HConseq with
      (eta1 := eta) (eta2 := svt_event_probability r gamma).
    - unfold pformula_valid.
      intro ps.
      intro Hadm.
      cbn [p_and p_not psatisfies].
      tauto.
    - exact Hbranch.
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
  }
  assert (Hrigid :
    hoare_derivable (p_and eta (svt_rigid_constant y r)) s
      (svt_rigid_constant y r)).
  {
    eapply HConseq with
      (eta1 := svt_rigid_constant y r)
      (eta2 := svt_rigid_constant y r).
    - unfold pformula_valid.
      intro ps.
      intro Hadm.
      cbn [p_and p_not psatisfies].
      tauto.
    - apply HFree.
      apply svt_rigid_constant_analytical.
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
  }
  eapply HConseq with
    (eta1 := p_and eta (svt_rigid_constant y r))
    (eta2 := p_and (svt_event_probability r gamma)
      (svt_rigid_constant y r)).
  - unfold pformula_valid.
    intro ps; cbn [psatisfies]; tauto.
  - apply HAnd; assumption.
  - unfold pformula_valid, svt_event_probability, svt_rigid_constant.
    intro ps.
    intro Hadm.
    cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
    intuition lra.
Qed.

(** A local exact conditional rule.  The rigid variables record the two
    branch masses, [HIfEq] adds them, [HFree]/[HAnd] retain their constant
    values, and [HElimv] removes the auxiliary names. *)
Lemma svt_if_constants :
  forall (eta1 eta2 : PFormula) (guard gamma : CFormula)
    (s1 s2 : Cmd) (r1 r2 : R),
    {{ $(eta1) }} $(s1) {{ $(svt_event_probability r1 gamma) }} ->
    {{ $(eta2) }} $(s2) {{ $(svt_event_probability r2 gamma) }} ->
    {{ $(subst_prob_pformula svt_y_then [[ $(r1) ]]
          (subst_prob_pformula svt_y_else [[ $(r2) ]]
            (if_precondition eta1 eta2 guard))) }}
      if $(guard) then $(s1) else $(s2) end
    {{ $(svt_event_probability (r1 + r2) gamma) }}.
Proof.
  intros eta1 eta2 guard gamma s1 s2 r1 r2 Hbranch1 Hbranch2.
  set (base := if_precondition eta1 eta2 guard).
  set (eq1 := svt_rigid_constant svt_y_then r1).
  set (eq2 := svt_rigid_constant svt_y_else r2).
  assert (Hif :
    hoare_derivable
      (if_precondition (p_and eta1 eq1) (p_and eta2 eq2) guard)
      (CIf guard s1 s2)
      (p_eq (PAdd (PVar svt_y_then) (PVar svt_y_else))
        (PExpect (QIndicator gamma)))).
  {
    apply HIfEq with
      (eta1 := p_and eta1 eq1) (eta2 := p_and eta2 eq2).
    - unfold eq1.
      apply svt_add_rigid_constant.
      exact Hbranch1.
    - unfold eq2.
      apply svt_add_rigid_constant.
      exact Hbranch2.
  }
  set (with_constants := p_and (p_and base eq1) eq2).
  assert (Hif_from_constants :
    hoare_derivable with_constants (CIf guard s1 s2)
      (p_eq (PAdd (PVar svt_y_then) (PVar svt_y_else))
        (PExpect (QIndicator gamma)))).
  {
    eapply HConseq with
      (eta1 := if_precondition (p_and eta1 eq1) (p_and eta2 eq2) guard)
      (eta2 := p_eq (PAdd (PVar svt_y_then) (PVar svt_y_else))
        (PExpect (QIndicator gamma))).
    - unfold pformula_valid, with_constants, base, eq1, eq2,
        if_precondition, svt_rigid_constant.
      intro ps.
      intro Hadm.
      cbn [condition_pformula condition_pterm p_and p_not p_eq
        psatisfies pterm_eval] in *.
      intuition lra.
    - exact Hif.
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
  }
  assert (Hconstants :
    hoare_derivable with_constants (CIf guard s1 s2) (p_and eq1 eq2)).
  {
    eapply HConseq with (eta1 := p_and eq1 eq2) (eta2 := p_and eq1 eq2).
    - unfold pformula_valid, with_constants.
      intro ps.
      intro Hadm.
      cbn [p_and p_not psatisfies].
      tauto.
    - apply HFree.
      unfold eq1, eq2.
      cbn [svt_rigid_constant p_eq p_and p_not
        pformula_analytical pterm_analytical].
      tauto.
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
  }
  assert (Hwithout_rigids :
    hoare_derivable with_constants (CIf guard s1 s2)
      (svt_event_probability (r1 + r2) gamma)).
  {
    eapply HConseq with
      (eta1 := with_constants)
      (eta2 := p_and
        (p_eq (PAdd (PVar svt_y_then) (PVar svt_y_else))
          (PExpect (QIndicator gamma)))
        (p_and eq1 eq2)).
    - unfold pformula_valid.
      intro ps; cbn [psatisfies]; tauto.
    - apply HAnd; assumption.
    - unfold pformula_valid, svt_event_probability, eq1, eq2,
        svt_rigid_constant.
      intro ps.
      intro Hadm.
      cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
      intuition lra.
  }
  assert (Helim_else :
    hoare_derivable
      (subst_prob_pformula svt_y_else (PConst r2)
        (p_and base eq1))
      (CIf guard s1 s2)
      (svt_event_probability (r1 + r2) gamma)).
  {
    eapply HElimv with
      (eta1 := p_and base eq1) (y := svt_y_else) (p := PConst r2).
    - change (hoare_derivable with_constants (CIf guard s1 s2)
        (svt_event_probability (r1 + r2) gamma)).
      exact Hwithout_rigids.
    - cbn [prob_logic_var_occurs_pterm]; tauto.
    - cbn [svt_event_probability p_eq p_and p_not
        prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm].
      tauto.
  }
  assert (Helim_then :
    hoare_derivable
      (subst_prob_pformula svt_y_then (PConst r1)
        (subst_prob_pformula svt_y_else (PConst r2) base))
      (CIf guard s1 s2)
      (svt_event_probability (r1 + r2) gamma)).
  {
    eapply HElimv with
      (eta1 := subst_prob_pformula svt_y_else (PConst r2) base)
      (y := svt_y_then) (p := PConst r1).
    - change (hoare_derivable
        (subst_prob_pformula svt_y_else (PConst r2) (p_and base eq1))
        (CIf guard s1 s2)
        (svt_event_probability (r1 + r2) gamma)).
      exact Helim_else.
    - cbn [prob_logic_var_occurs_pterm]; tauto.
    - cbn [svt_event_probability p_eq p_and p_not
        prob_logic_var_occurs_pformula prob_logic_var_occurs_pterm].
      tauto.
  }
  unfold base in Helim_then.
  exact Helim_then.
Qed.

Lemma svt_laplace_constant_valid :
  forall (location : Term) (scale : R),
    (0 < scale)%R ->
    pformula_valid
      [[ almost_sure[$(distribution_valid_formula
          <{ laplace ( $(location), $(scale) ) }>)] ]].
Proof.
  intros location scale Hscale.
  unfold pformula_valid.
  intro ps.
  intro Hadm.
  assert (Heq :
    expectation (pstate_measure ps)
      (q_eval
        (QIndicator
          (distribution_valid_formula
            (Laplace location (TConst scale))))) =
    expectation (pstate_measure ps) (q_eval (QIndicator c_true))).
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

Lemma svt_laplace_sample :
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
    intro Hadm.
    cbn [psatisfies].
    intro Hpre.
    apply (svt_laplace_constant_valid location scale Hscale ps).
Qed.

Definition svt_output_probability (r : R) : PFormula :=
  svt_event_probability r svt_bot_top.

Definition svt_inner_true_pre (p : R) : PFormula :=
  subst_bool_pformula svt_out2 <{ true }> (svt_output_probability p).

Definition svt_inner_false_pre : PFormula :=
  svt_output_probability 0.

Definition svt_inner_if_pre (p : R) : PFormula :=
  subst_prob_pformula svt_y_then [[ $(p) ]]
    (subst_prob_pformula svt_y_else [[ 0 ]]
      (if_precondition (svt_inner_true_pre p) svt_inner_false_pre
        <{ svt_above2 }>)).

Definition svt_after_noisy2 (p : R) : PFormula :=
  subst_bool_pformula svt_above2 svt_second_comparison
    (svt_inner_if_pre p).

Definition svt_before_noisy2 (epsilon p : R) : PFormula :=
  sample_pformula svt_noisy2
    (svt_query_distribution epsilon svt_q2)
    (svt_after_noisy2 p).

Lemma svt_inner_if_derivable :
  forall p : R,
    {{ $(svt_inner_if_pre p) }}
      if svt_above2 then svt_out2 b= true else skip end
    {{ $(svt_output_probability p) }}.
Proof.
  intro p.
  unfold svt_inner_if_pre, svt_output_probability.
  replace p with (p + 0)%R at 3 by ring.
  apply svt_if_constants.
  - unfold svt_inner_true_pre.
    apply HBoolAssign.
  - unfold svt_inner_false_pre.
    apply HSkip.
Qed.

Lemma svt_second_iteration_derivable :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(svt_before_noisy2 epsilon p) }}
      $(svt_second_iteration epsilon)
    {{ $(svt_output_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold svt_second_iteration, svt_before_noisy2,
    svt_query_distribution.
  eapply HSeq with (eta2 := svt_after_noisy2 p).
  - apply svt_laplace_sample.
    apply svt_query_scale_positive; exact Hepsilon.
  - eapply HSeq with (eta2 := svt_inner_if_pre p).
    + unfold svt_after_noisy2.
      apply HBoolAssign.
    + apply svt_inner_if_derivable.
Qed.

Definition svt_outer_true_pre : PFormula :=
  subst_bool_pformula svt_out1 <{ true }> (svt_output_probability 0).

Definition svt_outer_if_pre (epsilon p : R) : PFormula :=
  subst_prob_pformula svt_y_then [[ 0 ]]
    (subst_prob_pformula svt_y_else [[ $(p) ]]
      (if_precondition svt_outer_true_pre
        (svt_before_noisy2 epsilon p) <{ svt_above1 }>)).

Definition svt_after_noisy1 (epsilon p : R) : PFormula :=
  subst_bool_pformula svt_above1 svt_first_comparison
    (svt_outer_if_pre epsilon p).

Definition svt_before_noisy1 (epsilon p : R) : PFormula :=
  sample_pformula svt_noisy1
    (svt_query_distribution epsilon svt_q1)
    (svt_after_noisy1 epsilon p).

Definition svt_before_threshold (epsilon p : R) : PFormula :=
  sample_pformula svt_threshold (svt_threshold_distribution epsilon)
    (svt_before_noisy1 epsilon p).

Definition svt_before_output2 (epsilon p : R) : PFormula :=
  subst_bool_pformula svt_out2 <{ false }>
    (svt_before_threshold epsilon p).

Definition svt_generic_pre (epsilon p : R) : PFormula :=
  subst_bool_pformula svt_out1 <{ false }>
    (svt_before_output2 epsilon p).

Lemma svt_outer_if_derivable :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(svt_outer_if_pre epsilon p) }}
      if svt_above1 then svt_out1 b= true
      else $(svt_second_iteration epsilon)
      end
    {{ $(svt_output_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold svt_outer_if_pre, svt_output_probability.
  replace p with (0 + p)%R at 3 by ring.
  apply svt_if_constants.
  - unfold svt_outer_true_pre.
    apply HBoolAssign.
  - apply svt_second_iteration_derivable.
    exact Hepsilon.
Qed.

Theorem svt_generic_wp_derivable :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(svt_generic_pre epsilon p) }}
      $(svt_two_queries epsilon)
    {{ $(svt_output_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold svt_two_queries, svt_generic_pre.
  eapply HSeq with (eta2 := svt_before_output2 epsilon p).
  - apply HBoolAssign.
  - eapply HSeq with (eta2 := svt_before_threshold epsilon p).
    + unfold svt_before_output2.
      apply HBoolAssign.
    + eapply HSeq with (eta2 := svt_before_noisy1 epsilon p).
      * unfold svt_before_threshold, svt_threshold_distribution.
        apply svt_laplace_sample.
        apply svt_threshold_scale_positive; exact Hepsilon.
      * eapply HSeq with (eta2 := svt_after_noisy1 epsilon p).
        -- unfold svt_before_noisy1, svt_query_distribution.
           apply svt_laplace_sample.
           apply svt_query_scale_positive; exact Hepsilon.
        -- eapply HSeq with (eta2 := svt_outer_if_pre epsilon p).
           ++ unfold svt_after_noisy1.
              apply HBoolAssign.
           ++ apply svt_outer_if_derivable.
              exact Hepsilon.
Qed.

Definition svt_concrete_pre (epsilon p : R) : PFormula :=
  subst_real_pformula svt_q1 <{ 0 }>
    (subst_real_pformula svt_q2 <{ 1 }>
      (svt_generic_pre epsilon p)).

Theorem svt_concrete_wp_derivable :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(svt_concrete_pre epsilon p) }}
      $(svt_01 epsilon)
    {{ $(svt_output_probability p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold svt_01, svt_concrete_pre.
  eapply HSeq with
    (eta2 := subst_real_pformula svt_q2 (TConst 1)
      (svt_generic_pre epsilon p)).
  - apply HRealAssign.
  - eapply HSeq with (eta2 := svt_generic_pre epsilon p).
    + apply HRealAssign.
    + apply svt_generic_wp_derivable.
      exact Hepsilon.
Qed.

Lemma svt_path_construct_01_eval :
  forall (epsilon : R) (v : state),
    q_eval (svt_path_construct_01 epsilon) v =
      svt_nested_integral epsilon.
Proof.
  intros epsilon v.
  unfold svt_path_construct_01, svt_nested_integral,
    laplace_density_R, svt_threshold_distribution,
    svt_query_distribution, svt_path_event, c_and, c_not, c_lt.
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
  unfold svt_threshold, svt_noisy1, svt_noisy2.
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

Definition svt_symbolic_pre (epsilon p : R) : PFormula :=
  [[ $(normalized) /\ E[$(svt_path_construct epsilon)] = $(p) ]].

(** The three expectation constructs occurring in the generated weakest
    precondition: an impossible first-true branch, the desired path, and an
    impossible second-false branch. *)
Definition svt_wp_outer_zero_construct (epsilon : R) : PConstruct :=
  subst_bool_pconstruct svt_out1 <{ false }>
    (subst_bool_pconstruct svt_out2 <{ false }>
      [[
        integral svt_threshold ~ $(svt_threshold_distribution epsilon),
        integral svt_noisy1 ~ $(svt_query_distribution epsilon svt_q1),
        $(subst_bool_pconstruct svt_above1 svt_first_comparison
          (condition_pconstruct
            [[ indicator[$(subst_bool_cformula svt_out1 <{ true }> svt_bot_top)] ]]
            <{ svt_above1 }>))
      ]]).

Definition svt_wp_path_construct (epsilon : R) : PConstruct :=
  subst_bool_pconstruct svt_out1 <{ false }>
    (subst_bool_pconstruct svt_out2 <{ false }>
      [[
        integral svt_threshold ~ $(svt_threshold_distribution epsilon),
        integral svt_noisy1 ~ $(svt_query_distribution epsilon svt_q1),
        $(subst_bool_pconstruct svt_above1 svt_first_comparison
          (condition_pconstruct
            [[
              integral svt_noisy2 ~ $(svt_query_distribution epsilon svt_q2),
              $(subst_bool_pconstruct svt_above2 svt_second_comparison
                (condition_pconstruct
                  [[ indicator[$(subst_bool_cformula
                    svt_out2 <{ true }> svt_bot_top)] ]]
                  <{ svt_above2 }>))
            ]]
            <{ ~ svt_above1 }>))
      ]]).

Definition svt_wp_inner_zero_construct (epsilon : R) : PConstruct :=
  subst_bool_pconstruct svt_out1 <{ false }>
    (subst_bool_pconstruct svt_out2 <{ false }>
      [[
        integral svt_threshold ~ $(svt_threshold_distribution epsilon),
        integral svt_noisy1 ~ $(svt_query_distribution epsilon svt_q1),
        $(subst_bool_pconstruct svt_above1 svt_first_comparison
          (condition_pconstruct
            [[
              integral svt_noisy2 ~ $(svt_query_distribution epsilon svt_q2),
              $(subst_bool_pconstruct svt_above2 svt_second_comparison
                (condition_pconstruct
                  [[ indicator[$(svt_bot_top)] ]]
                  <{ ~ svt_above2 }>))
            ]]
            <{ ~ svt_above1 }>))
      ]]).

Lemma svt_generic_pre_shape :
  forall epsilon p : R,
    svt_generic_pre epsilon p =
      [[ 0 = E[$(svt_wp_outer_zero_construct epsilon)] /\
         $(p) = E[$(svt_wp_path_construct epsilon)] /\
         0 = E[$(svt_wp_inner_zero_construct epsilon)] ]].
Proof.
  intros epsilon p.
  unfold svt_generic_pre, svt_before_output2, svt_before_threshold,
    svt_before_noisy1, svt_after_noisy1, svt_outer_if_pre,
    svt_outer_true_pre, svt_before_noisy2, svt_after_noisy2,
    svt_inner_if_pre, svt_inner_true_pre, svt_inner_false_pre,
    svt_output_probability, svt_event_probability,
    svt_wp_outer_zero_construct, svt_wp_path_construct,
    svt_wp_inner_zero_construct, if_precondition.
  cbn [subst_prob_pformula subst_prob_pterm condition_pformula
    condition_pterm sample_pformula sample_pterm subst_bool_pformula
    subst_bool_pterm].
  reflexivity.
Qed.

Lemma svt_wp_path_construct_eval :
  forall (epsilon : R) (v : state),
    q_eval (svt_wp_path_construct epsilon) v =
      q_eval (svt_path_construct epsilon) v.
Proof.
  intros epsilon v.
  unfold svt_wp_path_construct, svt_path_construct,
    svt_threshold_distribution, svt_query_distribution,
    svt_first_comparison, svt_second_comparison, svt_bot_top,
    svt_path_event, svt_q1, svt_q2, svt_threshold, svt_noisy1,
    svt_noisy2, svt_above1, svt_above2, svt_out1, svt_out2.
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

Lemma svt_wp_outer_zero_construct_eval :
  forall (epsilon : R) (v : state),
    q_eval (svt_wp_outer_zero_construct epsilon) v = 0%R.
Proof.
  intros epsilon v.
  unfold svt_wp_outer_zero_construct, svt_threshold_distribution,
    svt_query_distribution, svt_first_comparison, svt_bot_top,
    svt_q1, svt_threshold, svt_noisy1, svt_above1,
    svt_out1, svt_out2.
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

Lemma svt_wp_inner_zero_construct_eval :
  forall (epsilon : R) (v : state),
    q_eval (svt_wp_inner_zero_construct epsilon) v = 0%R.
Proof.
  intros epsilon v.
  unfold svt_wp_inner_zero_construct, svt_threshold_distribution,
    svt_query_distribution, svt_first_comparison, svt_second_comparison,
    svt_bot_top, svt_q1, svt_q2, svt_threshold, svt_noisy1,
    svt_noisy2, svt_above1, svt_above2, svt_out1, svt_out2.
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

Lemma svt_symbolic_pre_implies_wp :
  forall epsilon p : R,
    pformula_valid
      [[ $(svt_symbolic_pre epsilon p) -> $(svt_generic_pre epsilon p) ]].
Proof.
  intros epsilon p.
  unfold pformula_valid.
  intro ps.
  intro Hadm.
  rewrite svt_generic_pre_shape.
  assert (Houter_zero :
    expectation (pstate_measure ps)
      (q_eval (svt_wp_outer_zero_construct epsilon)) = 0%R).
  {
    transitivity
      (expectation (pstate_measure ps) (fun _ : state => 0%R)).
    - apply expectation_extensional.
      intro v; apply svt_wp_outer_zero_construct_eval.
    - apply expectation_zero.
  }
  assert (Hinner_zero :
    expectation (pstate_measure ps)
      (q_eval (svt_wp_inner_zero_construct epsilon)) = 0%R).
  {
    transitivity
      (expectation (pstate_measure ps) (fun _ : state => 0%R)).
    - apply expectation_extensional.
      intro v; apply svt_wp_inner_zero_construct_eval.
    - apply expectation_zero.
  }
  assert (Hpath :
    expectation (pstate_measure ps)
      (q_eval (svt_wp_path_construct epsilon)) =
    expectation (pstate_measure ps)
      (q_eval (svt_path_construct epsilon))).
  {
    apply expectation_extensional.
    intro v; apply svt_wp_path_construct_eval.
  }
  unfold svt_symbolic_pre, normalized.
  cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
  intuition lra.
Qed.

Theorem svt_symbolic_hoare :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(svt_symbolic_pre epsilon p) }}
      $(svt_two_queries epsilon)
    {{ $(probability_of_bot_top_equals p) }}.
Proof.
  intros epsilon p Hepsilon.
  eapply HConseq with
    (eta1 := svt_generic_pre epsilon p)
    (eta2 := svt_output_probability p).
  - apply svt_symbolic_pre_implies_wp.
  - apply svt_generic_wp_derivable.
    exact Hepsilon.
  - unfold pformula_valid, svt_output_probability,
      svt_event_probability, probability_of_bot_top_equals.
    intro ps.
    intro Hadm.
    cbn [p_eq p_and p_not psatisfies pterm_eval] in *.
    intuition lra.
Qed.

Definition svt_symbolic_concrete_pre (epsilon p : R) : PFormula :=
  subst_real_pformula svt_q1 <{ 0 }>
    (subst_real_pformula svt_q2 <{ 1 }>
      (svt_symbolic_pre epsilon p)).

Theorem svt_symbolic_concrete_hoare :
  forall epsilon p : R,
    (0 < epsilon)%R ->
    {{ $(svt_symbolic_concrete_pre epsilon p) }}
      $(svt_01 epsilon)
    {{ $(probability_of_bot_top_equals p) }}.
Proof.
  intros epsilon p Hepsilon.
  unfold svt_01, svt_symbolic_concrete_pre.
  eapply HSeq with
    (eta2 := subst_real_pformula svt_q2 (TConst 1)
      (svt_symbolic_pre epsilon p)).
  - apply HRealAssign.
  - eapply HSeq with (eta2 := svt_symbolic_pre epsilon p).
    + apply HRealAssign.
    + apply svt_symbolic_hoare.
      exact Hepsilon.
Qed.

Lemma svt_path_substitution_01 :
  forall epsilon : R,
    subst_real_pconstruct svt_q1 <{ 0 }>
      (subst_real_pconstruct svt_q2 <{ 1 }>
        (svt_path_construct epsilon)) =
      svt_path_construct_01 epsilon.
Proof.
  intro epsilon.
  unfold svt_path_construct, svt_path_construct_01,
    svt_threshold_distribution, svt_query_distribution,
    svt_q1, svt_q2, svt_threshold, svt_noisy1, svt_noisy2.
  cbn [subst_real_pconstruct subst_real_pconstruct_fuel
    subst_real_distribution subst_real_term subst_real_cformula
    pconstruct_size pconstruct_real_program_vars
    distribution_real_program_vars term_real_program_vars
    cformula_real_program_vars List.in_dec real_program_var_eq_dec].
  reflexivity.
Qed.

Lemma svt_symbolic_concrete_pre_shape :
  forall epsilon p : R,
    svt_symbolic_concrete_pre epsilon p =
      [[ $(normalized) /\
         E[$(subst_real_pconstruct svt_q1 <{ 0 }>
           (subst_real_pconstruct svt_q2 <{ 1 }>
             (svt_path_construct epsilon)))] = $(p) ]].
Proof.
  intros epsilon p.
  unfold svt_symbolic_concrete_pre, svt_symbolic_pre, normalized.
  cbn [subst_real_pformula subst_real_pterm].
  reflexivity.
Qed.

Lemma normalized_implies_svt_concrete_pre :
  forall epsilon : R,
    (0 < epsilon)%R ->
    pformula_valid
      [[ $(normalized) ->
         $(svt_symbolic_concrete_pre epsilon
           (svt_r1 epsilon)) ]].
Proof.
  intros epsilon Hepsilon.
  unfold pformula_valid.
  intro ps.
  intro Hadm.
  rewrite svt_symbolic_concrete_pre_shape.
  rewrite svt_path_substitution_01.
  assert (Hpath :
    expectation (pstate_measure ps)
      (q_eval (svt_path_construct_01 epsilon)) =
    (svt_r1 epsilon *
      expectation (pstate_measure ps) (q_eval (QIndicator c_true)))%R).
  {
    transitivity
      (expectation (pstate_measure ps)
        (fun _ : state => svt_r1 epsilon)).
    - apply expectation_extensional.
      intro v.
      rewrite svt_path_construct_01_eval.
      apply svt_nested_integral_value.
      exact Hepsilon.
    - apply expectation_constant.
  }
  unfold normalized.
  cbn [p_and p_not p_eq psatisfies pterm_eval] in *.
  intro Hnormalized.
  assert (Hmass_upper :
    (expectation (pstate_measure ps) (q_eval (QIndicator c_true)) <= 1)%R).
  {
    apply NNPP; intro Hnot.
    apply Hnormalized.
    intro Hupper; contradiction.
  }
  assert (Hmass_lower :
    (1 <= expectation (pstate_measure ps) (q_eval (QIndicator c_true)))%R).
  {
    apply NNPP; intro Hnot.
    apply Hnormalized.
    intros Hupper Hlower; contradiction.
  }
  assert (Hmass :
    expectation (pstate_measure ps) (q_eval (QIndicator c_true)) = 1%R)
    by lra.
  assert (Hpath_value :
    expectation (pstate_measure ps) (q_eval (svt_path_construct_01 epsilon)) =
      svt_r1 epsilon).
  {
    rewrite Hpath, Hmass; ring.
  }
  assert (Hpath_upper :
    (expectation (pstate_measure ps)
      (q_eval (svt_path_construct_01 epsilon)) <= svt_r1 epsilon)%R)
    by lra.
  assert (Hpath_lower :
    (svt_r1 epsilon <= expectation (pstate_measure ps)
      (q_eval (svt_path_construct_01 epsilon)))%R)
    by lra.
  tauto.
Qed.

Theorem svt_01_bot_top_probability :
  forall epsilon : R,
    (0 < epsilon)%R ->
    {{ $(normalized) }}
      $(svt_01 epsilon)
    {{ $(probability_of_bot_top_equals (svt_r1 epsilon)) }}.
Proof.
  intros epsilon Hepsilon.
  eapply HConseq with
    (eta1 := svt_symbolic_concrete_pre epsilon (svt_r1 epsilon))
    (eta2 := probability_of_bot_top_equals (svt_r1 epsilon)).
  - apply normalized_implies_svt_concrete_pre.
    exact Hepsilon.
  - apply svt_symbolic_concrete_hoare.
    exact Hepsilon.
  - unfold pformula_valid.
    intro ps; cbn [psatisfies]; tauto.
Qed.
