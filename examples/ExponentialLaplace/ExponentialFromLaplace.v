(**
  ExponentialFromLaplace.v

  Program ([ef_prog b]):

      x <- sample(laplace(0, b));
      neg := (x < 0);
      if neg then e := (-1) * x else e := x end

  Triple ([ef_correct], for 0 <= t, 0 < b, and G such that the state-logic
  CDF formula [t3_cdf t b G] (HalfLaplaceRejection.v) is valid):

      t3_cdf t b G :=
        Pr[tt] = 1  ->  E[ integral z ~ exponential(1/b), 1_(z <= t) ] = G

      { Pr[tt] = 1 }  ef_prog b  { Pr[e < t] = G }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import MeasureIntegration CdfLibraryFacts.
Require Import CPHLFacts.ConstructFacts CPHLFacts.CalculationFacts.
Require Import CPHLFacts.ExponentialIntegrals.
Require Import CdfAssertions.
Require Import SampleBeforeLoop.
Require Import PersistentSampleLoop.
Require Import HalfLaplaceRejection.
Require Import TruncatedLaplaceRejection.
Require Import SVT.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program *)

Definition ef_x : RealProgramVar := real_program_var "ef_x".
Definition ef_e : RealProgramVar := real_program_var "ef_e".
Definition ef_neg : BoolProgramVar := bool_program_var "ef_neg".

Definition ef_minus_one : Term := TConst (-1).
Definition ef_negate : Term := <{ $(ef_minus_one) * ef_x }>.

Definition ef_noise (b : R) : Distribution := <{ laplace(0, b) }>.
Definition ef_sign : CFormula := <{ ef_x < 0 }>.

Definition ef_prog (b : R) : Cmd :=
  <{ ef_x   sample $(ef_noise b);
     ef_neg b= $(ef_sign);
     if ef_neg then ef_e := $(ef_negate) else ef_e := ef_x end }>.

(** The output event, and the source events the two branches turn it into. *)
Definition ef_out (t : R) : CFormula := <{ ef_e < t }>.
Definition ef_src_lo (t : R) : CFormula := <{ $(ef_negate) < t }>.
Definition ef_src_hi (t : R) : CFormula := <{ ef_x < t }>.

(** Both halves carry the same mass [(1 - r) / 2], where [r] is the
    exponential survival probability at [t]. *)
Definition ef_half (r : R) : R := (1 - r) / 2.

(** * What the two branch regions are *)

Lemma ef_sat_lo :
  forall (t z : R) (v : state),
    satisfies (update_real v ef_x z) <{ $(ef_src_lo t) /\ $(ef_sign) }> <->
    (- t < z /\ z < 0).
Proof.
  intros t z v.
  rewrite satisfies_c_and.
  unfold ef_src_lo, ef_sign, ef_negate, ef_minus_one, c_lt, c_not,
    update_real, update_real_values.
  cbn [satisfies term_eval real_program_values].
  rewrite !rpv_eq_dec_refl.
  split.
  - intro H; destruct H as [Hlo Hhi].
    split.
    + destruct (Rlt_dec (- t) z) as [Hd | Hd]; [exact Hd |].
      exfalso; apply Hlo; lra.
    + destruct (Rlt_dec z 0) as [Hd | Hd]; [exact Hd |].
      exfalso; apply Hhi; lra.
  - intro H; destruct H as [Hlo Hhi].
    split; intro Hf; lra.
Qed.

Lemma ef_sat_hi :
  forall (t z : R) (v : state),
    satisfies (update_real v ef_x z)
      <{ $(ef_src_hi t) /\ (~ $(ef_sign)) }> <->
    (0 <= z < t).
Proof.
  intros t z v.
  rewrite satisfies_c_and.
  unfold ef_src_hi, ef_sign, c_lt, c_not, update_real, update_real_values.
  cbn [satisfies term_eval real_program_values].
  rewrite !rpv_eq_dec_refl.
  split.
  - intro H; destruct H as [Hlt Hge].
    split.
    + destruct (Rle_dec 0 z) as [Hd | Hd]; [exact Hd |].
      exfalso; apply Hge; intro Hf; lra.
    + destruct (Rlt_dec z t) as [Hd | Hd]; [exact Hd |].
      exfalso; apply Hlt; lra.
  - intro H; destruct H as [Hge Hlt].
    split.
    + intro Hf; lra.
    + intro Hf; exact (Hf Hge).
Qed.

(** * Laplace masses of the two halves *)

(** The lower Laplace tail below [-t], by the proved exponential integral. *)
Lemma ef_lap_below_neg :
  forall b t : R, 0 < b -> 0 <= t ->
    lap_below 0 b (- t) = (1 / 2) * exp (- t / b).
Proof.
  intros b t Hb Ht.
  unfold lap_below, lap_density.
  transitivity
    (real_integral (fun z => (1 / (2 * b)) * (real_indicator (z < - t) * exp (/ b * z)))).
  - apply real_integral_extensional; intro z.
    destruct (Rlt_dec z (- t)) as [Hz | Hz].
    + rewrite !(real_indicator_true (z < - t)) by exact Hz.
      rewrite Rminus_0_r, Rabs_left by lra.
      replace (- - z / b) with (/ b * z) by (field; lra).
      ring.
    + rewrite !(real_indicator_false (z < - t)) by exact Hz; ring.
  - rewrite real_integral_scale
      by (apply real_integrable_exp_below; apply Rinv_0_lt_compat; exact Hb).
    change (real_integral (fun z => real_indicator (z < - t) * exp (/ b * z)))
      with (real_integral_below (- t) (fun z => exp (/ b * z))).
    rewrite real_integral_exp_below_proved
      by (apply Rinv_0_lt_compat; exact Hb).
    replace (- t / b) with (/ b * - t) by (field; lra).
    field; lra.
Qed.

Lemma ef_mass_hi :
  forall b t : R, 0 < b -> 0 <= t ->
    lap_window 0 b 0 t = ef_half (exp (- t / b)).
Proof.
  intros b t Hb Ht.
  rewrite lap_window_above by assumption.
  rewrite !lap_above_closed by (assumption || apply Rle_refl).
  replace (- 0 / b) with 0 by (field; lra).
  rewrite exp_0; unfold ef_half; field.
Qed.

Lemma ef_mass_lo :
  forall b t : R, 0 < b -> 0 <= t ->
    real_integral (fun z => lap_density 0 b z * real_indicator (- t < z /\ z < 0)) =
    ef_half (exp (- t / b)).
Proof.
  intros b t Hb Ht.
  destruct (Req_dec t 0) as [Ht0 | Ht0].
  - (* the region is empty *)
    subst t.
    replace (- 0 / b) with 0 by (field; lra).
    rewrite exp_0; unfold ef_half.
    replace ((1 - 1) / 2) with 0 by field.
    transitivity (real_integral (fun _ : R => 0)); [| exact real_integral_zero].
    apply real_integral_extensional; intro z.
    rewrite (real_indicator_false (- 0 < z /\ z < 0)) by lra; ring.
  - (* t > 0: the line splits into (-oo, -t], (-t, 0) and [0, +oo) *)
    set (dens := lap_density 0 b).
    set (f1 := fun z => dens z * real_indicator (z <= - t)).
    set (f2 := fun z => dens z * real_indicator (0 <= z)).
    set (g := fun z => dens z * real_indicator (- t < z /\ z < 0)).
    assert (Hi1 : real_integrable f1)
      by (apply (lap_masked_integrable 0 b Hb), real_measurable_atmost).
    assert (Hi2 : real_integrable f2)
      by (apply (lap_masked_integrable 0 b Hb), real_measurable_above).
    assert (Hi12 : real_integrable (fun z => f1 z + f2 z))
      by exact (@ConcreteMeasure.integrable_add _ RealIntegration.Space
                  RealIntegration.lebesgue _ _ Hi1 Hi2).
    assert (Hpt : forall z, g z + (f1 z + f2 z) = dens z).
    { intro z; unfold g, f1, f2.
      destruct (Rle_dec z (- t)) as [Hz | Hz].
      - rewrite (real_indicator_false (- t < z /\ z < 0)) by lra.
        rewrite (real_indicator_true (z <= - t)) by exact Hz.
        rewrite (real_indicator_false (0 <= z)) by lra; ring.
      - rewrite (real_indicator_false (z <= - t)) by exact Hz.
        destruct (Rle_dec 0 z) as [H0 | H0].
        + rewrite (real_indicator_false (- t < z /\ z < 0)) by lra.
          rewrite (real_indicator_true (0 <= z)) by exact H0; ring.
        + rewrite (real_indicator_true (- t < z /\ z < 0)) by lra.
          rewrite (real_indicator_false (0 <= z)) by exact H0; ring. }
    assert (Hig : real_integrable g).
    { apply (real_integrable_ext (fun z => dens z + (-1) * (f1 z + f2 z))).
      - intro z; rewrite <- (Hpt z); ring.
      - exact (@ConcreteMeasure.integrable_add _ RealIntegration.Space
                 RealIntegration.lebesgue _ _
                 (lap_density_integrable 0 b Hb)
                 (real_integrable_scale (-1) _ Hi12)). }
    assert (Htot : real_integral g + (real_integral f1 + real_integral f2) = 1).
    { rewrite <- real_integral_add by assumption.
      rewrite <- real_integral_add by assumption.
      rewrite <- (lap_density_total 0 b Hb).
      apply real_integral_extensional; exact Hpt. }
    change (real_integral f1) with (lap_atmost 0 b (- t)) in Htot.
    change (real_integral f2) with (lap_above 0 b 0) in Htot.
    rewrite lap_atmost_below, ef_lap_below_neg in Htot by assumption.
    rewrite lap_above_closed in Htot by (assumption || apply Rle_refl).
    replace (- 0 / b) with 0 in Htot by (field; lra).
    rewrite exp_0 in Htot.
    unfold ef_half; fold g; lra.
Qed.

(** * Evaluating the two sampled integrals *)

Lemma ef_integral_hi :
  forall (t b : R) (v : state),
    0 <= t -> 0 < b ->
    q_eval
      [[ integral ef_x ~ $(ef_noise b),
         indicator[$(ef_src_hi t) /\ (~ $(ef_sign))] ]] v =
    ef_half (exp (- t / b)).
Proof.
  intros t b v Ht Hb.
  unfold ef_noise.
  rewrite (q_eval_laplace_indicator ef_x 0 b _ (fun z => 0 <= z < t) v Hb
             (fun z => ef_sat_hi t z v)).
  exact (ef_mass_hi b t Hb Ht).
Qed.

Lemma ef_integral_lo :
  forall (t b : R) (v : state),
    0 <= t -> 0 < b ->
    q_eval
      [[ integral ef_x ~ $(ef_noise b),
         indicator[$(ef_src_lo t) /\ $(ef_sign)] ]] v =
    ef_half (exp (- t / b)).
Proof.
  intros t b v Ht Hb.
  unfold ef_noise.
  rewrite (q_eval_laplace_indicator ef_x 0 b _ (fun z => - t < z /\ z < 0) v Hb
             (fun z => ef_sat_lo t z v)).
  exact (ef_mass_lo b t Hb Ht).
Qed.

(** * Program reasoning

    From here the shape is the same as LaplaceFromExponential.v: two real
    assignments, [svt_if_constants] to add the branch masses, then the
    boolean assignment and the sample. *)

Lemma ef_then_branch :
  forall r t : R,
    {{ $(svt_event_probability r (ef_src_lo t)) }}
      ef_e := $(ef_negate)
    {{ $(svt_event_probability r (ef_out t)) }}.
Proof.
  intros r t.
  replace (svt_event_probability r (ef_src_lo t))
    with (subst_real_pformula ef_e ef_negate
           (svt_event_probability r (ef_out t))).
  - apply HRealAssign.
  - unfold svt_event_probability, ef_out, ef_src_lo, p_eq, c_lt.
    cbn [subst_real_pformula subst_real_pterm subst_real_pconstruct
         subst_real_cformula subst_real_term].
    try rewrite rpv_eq_dec_refl.
    reflexivity.
Qed.

Lemma ef_else_branch :
  forall r t : R,
    {{ $(svt_event_probability r (ef_src_hi t)) }}
      ef_e := ef_x
    {{ $(svt_event_probability r (ef_out t)) }}.
Proof.
  intros r t.
  replace (svt_event_probability r (ef_src_hi t))
    with (subst_real_pformula ef_e (TProgVar ef_x)
           (svt_event_probability r (ef_out t))).
  - apply HRealAssign.
  - unfold svt_event_probability, ef_out, ef_src_hi, p_eq, c_lt.
    cbn [subst_real_pformula subst_real_pterm subst_real_pconstruct
         subst_real_cformula subst_real_term].
    try rewrite rpv_eq_dec_refl.
    reflexivity.
Qed.

Lemma ef_if_step :
  forall r1 r2 t : R,
    {{ $(if_precondition
           (svt_event_probability r1 (ef_src_lo t))
           (svt_event_probability r2 (ef_src_hi t))
           <{ ef_neg }>) }}
      if ef_neg then ef_e := $(ef_negate) else ef_e := ef_x end
    {{ $(svt_event_probability (r1 + r2) (ef_out t)) }}.
Proof.
  intros r1 r2 t.
  pose proof
    (svt_if_constants
       (svt_event_probability r1 (ef_src_lo t))
       (svt_event_probability r2 (ef_src_hi t))
       (FProgBool ef_neg) (ef_out t)
       (CRealAssign ef_e ef_negate)
       (CRealAssign ef_e (TProgVar ef_x))
       r1 r2
       (ef_then_branch r1 t) (ef_else_branch r2 t)) as H.
  cbn [subst_prob_pformula subst_prob_pterm if_precondition
       condition_pformula condition_pterm
       svt_event_probability p_eq p_and p_not] in H.
  exact H.
Qed.

(** Reshaping lemmas, all definitional. *)

Lemma ef_condition_p_eq_const :
  forall (c : R) (gamma guard : CFormula),
    condition_pformula [[ $(c) = Pr[$(gamma)] ]] guard =
    [[ $(c) = Pr[$(gamma) /\ $(guard)] ]].
Proof. reflexivity. Qed.

Lemma ef_subst_p_and :
  forall (b : BoolProgramVar) (beta : CFormula) (eta1 eta2 : PFormula),
    subst_bool_pformula b beta [[ $(eta1) /\ $(eta2) ]] =
    [[ $(subst_bool_pformula b beta eta1)
       /\ $(subst_bool_pformula b beta eta2) ]].
Proof. reflexivity. Qed.

Lemma ef_subst_p_eq_const :
  forall (b : BoolProgramVar) (beta : CFormula) (c : R) (q : PConstruct),
    subst_bool_pformula b beta [[ $(c) = E[$(q)] ]] =
    [[ $(c) = E[$(subst_bool_pconstruct b beta q)] ]].
Proof. reflexivity. Qed.

Lemma ef_subst_lo :
  forall t : R,
    subst_bool_pconstruct ef_neg ef_sign
      [[ indicator[$(ef_src_lo t) /\ ef_neg] ]] =
    [[ indicator[$(ef_src_lo t) /\ $(ef_sign)] ]].
Proof. reflexivity. Qed.

Lemma ef_subst_hi :
  forall t : R,
    subst_bool_pconstruct ef_neg ef_sign
      [[ indicator[$(ef_src_hi t) /\ (~ ef_neg)] ]] =
    [[ indicator[$(ef_src_hi t) /\ (~ $(ef_sign))] ]].
Proof. reflexivity. Qed.

Lemma ef_sample_p_and :
  forall (x : RealProgramVar) (d : Distribution) (eta1 eta2 : PFormula),
    sample_pformula x d [[ $(eta1) /\ $(eta2) ]] =
    [[ $(sample_pformula x d eta1) /\ $(sample_pformula x d eta2) ]].
Proof. reflexivity. Qed.

Lemma ef_sample_p_eq_const :
  forall (x : RealProgramVar) (d : Distribution) (c : R) (q : PConstruct),
    sample_pformula x d [[ $(c) = E[$(q)] ]] =
    [[ $(c) = E[integral x ~ $(d), $(q)] ]].
Proof. reflexivity. Qed.

Lemma ef_noise_valid_under :
  forall (b : R) (eta : PFormula),
    0 < b ->
    pformula_valid
      [[ $(eta) -> almost_sure[$(distribution_valid_formula (ef_noise b))] ]].
Proof.
  intros b eta Hb ps Hadm _.
  refine (p_almost_sure_of_pointwise _ _ ps Hadm).
  intro v.
  unfold ef_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The folded sampler

    Each half of the fold carries half of the exponential CDF [G].  The only
    link between [G] and the program is the CDF hypothesis, read at the
    current state inside the validity side condition. *)

Theorem ef_correct :
  forall t b G : R,
    0 <= t -> 0 < b ->
    pformula_valid (t3_cdf t b G) ->
    {{ Pr[true] = 1 }}
      $(ef_prog b)
    {{ Pr[$(ef_out t)] = $(G) }}.
Proof.
  intros t b G Ht Hb HG.
  unfold ef_prog.
  set (P :=
    if_precondition
      (svt_event_probability (G / 2) (ef_src_lo t))
      (svt_event_probability (G / 2) (ef_src_hi t))
      (FProgBool ef_neg)).
  set (P2 := subst_bool_pformula ef_neg ef_sign P).
  eapply HConseq with
    (eta1 := sample_pformula ef_x (ef_noise b) P2)
    (eta2 := svt_event_probability (G / 2 + G / 2) (ef_out t)).
  - (* validity: each half of the sampled mass is half the CDF *)
    intros ps Hadm.
    cbn [psatisfies]; intro Hpre.
    apply psatisfies_p_eq in Hpre.
    cbn [pterm_eval] in Hpre.
    pose proof (valid_unit_eq ps (t3_cdf_q t b) G Hadm Hpre HG) as HGps.
    assert (Hcdf : expectation (pstate_measure ps) (q_eval (t3_cdf_q t b)) =
                   (1 - exp (- t / b))%R).
    { rewrite (t3_expect_const ps _ (1 - exp (- t / b))%R Hpre); [reflexivity |].
      intro v; apply t3_cdf_q_eval; assumption. }
    unfold P2, P, if_precondition, svt_event_probability.
    rewrite !ef_condition_p_eq_const.
    rewrite ef_subst_p_and, !ef_subst_p_eq_const, ef_subst_lo, ef_subst_hi.
    rewrite ef_sample_p_and, !ef_sample_p_eq_const.
    apply psatisfies_p_and; split; apply psatisfies_p_eq;
      cbn [pterm_eval].
    + rewrite (t3_expect_const ps _ (ef_half (exp (- t / b))) Hpre)
        by (intro v; apply ef_integral_lo; assumption).
      unfold ef_half; rewrite <- HGps, Hcdf; field.
    + rewrite (t3_expect_const ps _ (ef_half (exp (- t / b))) Hpre)
        by (intro v; apply ef_integral_hi; assumption).
      unfold ef_half; rewrite <- HGps, Hcdf; field.
  - eapply HSeq with (eta2 := P2).
    + apply HRealSample.
      * intros ps Hadm; cbn [psatisfies]; intro H; exact H.
      * apply ef_noise_valid_under; exact Hb.
    + eapply HSeq with (eta2 := P).
      * unfold P2; apply HBoolAssign.
      * unfold P; apply ef_if_step.
  - (* both halves together are the CDF *)
    intros ps Hadm.
    unfold svt_event_probability.
    intro Hpost.
    apply psatisfies_p_eq in Hpost.
    cbn [pterm_eval] in Hpost.
    apply psatisfies_p_eq.
    cbn [pterm_eval].
    lra.
Qed.
