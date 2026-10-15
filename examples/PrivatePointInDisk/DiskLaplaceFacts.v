(**
  DiskLaplaceFacts.v -- analytic support for the PrivatePointInDisk examples.
  No program, no triple.
*)

From Stdlib Require Import Reals Lra.
Require Import MeasureIntegration CPHL.
Require Import CPHLFacts.ConstructFacts CPHLFacts.CalculationFacts.
Require Import CPHLFacts.DistributionFacts.
Require Import CPHLFacts.ExponentialIntegrals.
Require Import CdfLibraryFacts.
Require Import CdfAssertions.

Open Scope R_scope.

(** * Closed forms of the Laplace tails at an arbitrary location *)

Lemma disk_lap_above_closed :
  forall loc b c : R, 0 < b -> loc <= c ->
    lap_above loc b c = (1 / 2) * exp (- (c - loc) / b).
Proof.
  intros loc b c Hb Hc.
  unfold lap_above, lap_density.
  transitivity
    (real_integral (fun z => ((1 / (2 * b)) * exp (loc / b)) *
                             (real_indicator (c <= z) * exp (- / b * z)))).
  - apply real_integral_extensional; intro z.
    destruct (Rle_dec c z) as [Hz | Hz].
    + rewrite (real_indicator_true (c <= z)) by exact Hz.
      rewrite Rabs_right by lra.
      replace (- (z - loc) / b) with (loc / b + - / b * z) by (field; lra).
      rewrite exp_plus; ring.
    + rewrite (real_indicator_false (c <= z)) by exact Hz; ring.
  - rewrite real_integral_scale
      by (apply real_integrable_exp_above;
          apply Ropp_lt_gt_0_contravar, Rinv_0_lt_compat; exact Hb).
    change (real_integral (fun z => real_indicator (c <= z) * exp (- / b * z)))
      with (real_integral_above c (fun z => exp (- / b * z))).
    rewrite real_integral_exp_above_proved
      by (apply Ropp_lt_gt_0_contravar, Rinv_0_lt_compat; exact Hb).
    replace (- (c - loc) / b) with (loc / b + - / b * c) by (field; lra).
    rewrite exp_plus; field; lra.
Qed.

Lemma disk_lap_below_closed :
  forall loc b c : R, 0 < b -> c <= loc ->
    lap_below loc b c = (1 / 2) * exp ((c - loc) / b).
Proof.
  intros loc b c Hb Hc.
  unfold lap_below, lap_density.
  transitivity
    (real_integral (fun z => ((1 / (2 * b)) * exp (- loc / b)) *
                             (real_indicator (z < c) * exp (/ b * z)))).
  - apply real_integral_extensional; intro z.
    destruct (Rlt_dec z c) as [Hz | Hz].
    + rewrite (real_indicator_true (z < c)) by exact Hz.
      rewrite Rabs_left by lra.
      replace (- - (z - loc) / b) with (- loc / b + / b * z) by (field; lra).
      rewrite exp_plus; ring.
    + rewrite (real_indicator_false (z < c)) by exact Hz; ring.
  - rewrite real_integral_scale
      by (apply real_integrable_exp_below; apply Rinv_0_lt_compat; exact Hb).
    change (real_integral (fun z => real_indicator (z < c) * exp (/ b * z)))
      with (real_integral_below c (fun z => exp (/ b * z))).
    rewrite real_integral_exp_below_proved
      by (apply Rinv_0_lt_compat; exact Hb).
    replace ((c - loc) / b) with (- loc / b + / b * c) by (field; lra).
    rewrite exp_plus; field; lra.
Qed.

(** The Laplace CDF at [c] about [loc], as a function of [c - loc]. *)
Definition disk_F (b t : R) : R :=
  if Rle_dec t 0 then (1 / 2) * exp (t / b)
  else 1 - (1 / 2) * exp (- t / b).

Lemma disk_lap_atmost_closed :
  forall loc b c : R, 0 < b -> lap_atmost loc b c = disk_F b (c - loc).
Proof.
  intros loc b c Hb.
  rewrite (lap_atmost_below loc b Hb).
  unfold disk_F.
  destruct (Rle_dec (c - loc) 0) as [H | H].
  - apply disk_lap_below_closed; lra.
  - pose proof (lap_below_above loc b Hb c) as Hs.
    rewrite (disk_lap_above_closed loc b c Hb) in Hs by lra.
    lra.
Qed.

(** Translation invariance of the Laplace CDF. *)
Lemma disk_lap_atmost_shift :
  forall loc b c : R, 0 < b -> lap_atmost loc b c = lap_atmost 0 b (c - loc).
Proof.
  intros loc b c Hb.
  rewrite !disk_lap_atmost_closed by exact Hb.
  f_equal; ring.
Qed.

Lemma disk_F_nonpos :
  forall b x : R, x <= 0 -> disk_F b x = (1 / 2) * exp (x / b).
Proof.
  intros b x Hx; unfold disk_F.
  destruct (Rle_dec x 0); [reflexivity | lra].
Qed.

Lemma disk_F_nonneg :
  forall b x : R, 0 < b -> 0 <= x -> disk_F b x = 1 - (1 / 2) * exp (- x / b).
Proof.
  intros b x Hb Hx; unfold disk_F.
  destruct (Rle_dec x 0) as [H | H].
  - assert (x = 0) by lra; subst x.
    replace (0 / b) with 0 by (field; lra).
    replace (- 0 / b) with 0 by (field; lra).
    rewrite exp_0; lra.
  - reflexivity.
Qed.

(** * Evaluating integral binders *)

(** A Laplace binder whose location is any term, read at the current state. *)
Lemma disk_laplace_indicator :
  forall (z : RealProgramVar) (t : Term) (loc b : R) (gamma : CFormula)
    (P : R -> Prop) (v : state),
    0 < b ->
    term_eval t v = loc ->
    (forall r, satisfies (update_real v z r) gamma <-> P r) ->
    q_eval (QIntegral z (Laplace t (TConst b)) (QIndicator gamma)) v =
    real_integral (fun r => lap_density loc b r * real_indicator (P r)).
Proof.
  intros z t loc b gamma P v Hb Ht HP.
  rewrite q_integral_density by (cbn [distribution_valid term_eval]; exact Hb).
  apply real_integral_extensional; intro r.
  rewrite q_eval_indicatorE.
  rewrite (real_indicator_extensional _ (P r)) by apply HP.
  cbn [distribution_density term_eval]; rewrite Ht; reflexivity.
Qed.

(** Integrating a construct that is constant across states returns it. *)
Lemma disk_integral_const :
  forall (x : RealProgramVar) (d : Distribution) (q : PConstruct)
    (v : state) (c : R),
    distribution_valid d v ->
    (forall w : state, q_eval q w = c) ->
    q_eval (QIntegral x d q) v = c.
Proof.
  intros x d q v c Hd Hc.
  rewrite q_integral_density by exact Hd.
  transitivity (real_integral (fun z => c * distribution_density d v z)).
  - apply real_integral_extensional; intro z; rewrite Hc; apply Rmult_comm.
  - rewrite real_integral_scale by (apply distribution_density_integrable; exact Hd).
    assert (H1 : real_integral (distribution_density d v) = 1)
      by exact (real_integral_distribution_density Hd).
    rewrite H1; ring.
Qed.

(** A half-open window under a Laplace density is a difference of CDFs. *)
Lemma disk_lap_window :
  forall loc b A B : R, 0 < b -> A <= B ->
    real_integral (fun z => lap_density loc b z * real_indicator (A <= z < B)) =
    lap_atmost loc b B - lap_atmost loc b A.
Proof.
  intros loc b A B Hb Hab.
  rewrite !(lap_atmost_below loc b Hb).
  unfold lap_below.
  assert (Hsum :
    real_integral (fun z => lap_density loc b z * real_indicator (A <= z < B)) +
    real_integral (fun z => lap_density loc b z * real_indicator (z < A)) =
    real_integral (fun z => lap_density loc b z * real_indicator (z < B))).
  { rewrite <- real_integral_add.
    - apply real_integral_extensional; intro z.
      destruct (Rlt_dec z A) as [H1 | H1].
      + rewrite (real_indicator_false (A <= z < B)) by lra.
        rewrite (real_indicator_true (z < A)) by lra.
        rewrite (real_indicator_true (z < B)) by lra; ring.
      + rewrite (real_indicator_false (z < A)) by lra.
        destruct (Rlt_dec z B) as [H2 | H2].
        * rewrite (real_indicator_true (A <= z < B)) by lra.
          rewrite (real_indicator_true (z < B)) by lra; ring.
        * rewrite (real_indicator_false (A <= z < B)) by lra.
          rewrite (real_indicator_false (z < B)) by lra; ring.
    - apply (lap_masked_integrable loc b Hb (fun z => A <= z < B)),
        real_measurable_between.
    - apply (lap_masked_integrable loc b Hb (fun z => z < A)),
        real_measurable_below. }
  lra.
Qed.
