(**
  NormalDistance.v

  Program ([nrm_prog px py cx cy b]):
      nrm_d := (px - cx)^2 + (py - cy)^2;
      nrm_n <- sample(gaussian(0, b));
      nrm_d := nrm_d + nrm_n;
      nrm_inside := (nrm_d < 1)
  Triple ([nrm_correct], for 0 < b and any precondition eta; post [nrm_post]):
      { eta }
        nrm_prog px py cx cy b
      { Pr[nrm_inside] = E[ integral nrm_z ~ gaussian(0, b),
                              indicator[nrm_z < 1 + -1 * ((px-cx)^2 + (py-cy)^2)] ] }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
Require Import CPHL.
Require Import CPHLFacts.DistributionFacts CPHLFacts.CalculationFacts.
Require Import SampleBeforeLoop.
Require Import HalfLaplaceRejection.
Require Import CdfAssertions.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program

    The four coordinates are Rocq reals, so the squared distance is a CLOSED
    term and the opening assignment makes the integral state-independent. *)

Definition nrm_d : RealProgramVar := real_program_var "nrm_d".
Definition nrm_n : RealProgramVar := real_program_var "nrm_n".
Definition nrm_z : RealProgramVar := real_program_var "nrm_z".
Definition nrm_inside : BoolProgramVar := bool_program_var "nrm_inside".

Definition nrm_minus_one : Term := TConst (-1).

Definition nrm_delta (u w : R) : Term := <{ $(u) + $(nrm_minus_one) * $(w) }>.

Definition nrm_sqdist (px py cx cy : R) : Term :=
  <{ ($(nrm_delta px cx) * $(nrm_delta px cx))
     + ($(nrm_delta py cy) * $(nrm_delta py cy)) }>.

Definition nrm_D (px py cx cy : R) : R :=
  ((px - cx) * (px - cx) + (py - cy) * (py - cy))%R.

(** The cutoff [1 - D], as a syntactic term. *)
Definition nrm_cut (px py cx cy : R) : Term :=
  <{ 1 + $(nrm_minus_one) * $(nrm_sqdist px py cx cy) }>.

Definition nrm_noise (b : R) : Distribution := <{ gaussian(0, b) }>.

Definition nrm_shift : Term := <{ nrm_d + nrm_n }>.

Definition nrm_test : CFormula := <{ nrm_d < 1 }>.

Definition nrm_prog (px py cx cy b : R) : Cmd :=
  <{ nrm_d      := $(nrm_sqdist px py cx cy);
     nrm_n      sample $(nrm_noise b);
     nrm_d      := $(nrm_shift);
     nrm_inside b= $(nrm_test) }>.

(** * Values of the closed terms *)

Lemma nrm_sqdist_value :
  forall (px py cx cy : R) (v : state),
    term_eval (nrm_sqdist px py cx cy) v = nrm_D px py cx cy.
Proof.
  intros px py cx cy v.
  unfold nrm_sqdist, nrm_delta, nrm_minus_one, nrm_D.
  cbn [term_eval]; ring.
Qed.

Lemma nrm_cut_value :
  forall (px py cx cy : R) (v : state),
    term_eval (nrm_cut px py cx cy) v = 1 - nrm_D px py cx cy.
Proof.
  intros px py cx cy v.
  unfold nrm_cut, nrm_minus_one.
  cbn [term_eval]; rewrite nrm_sqdist_value; ring.
Qed.

(** * The postcondition and its weakest precondition *)

(** The centred normal CDF at the cutoff, as a probabilistic construct. *)
Definition nrm_cdf_construct (px py cx cy b : R) : PConstruct :=
  [[ integral nrm_z ~ $(nrm_noise b),
     indicator[ nrm_z < $(nrm_cut px py cx cy) ] ]].

Definition nrm_post (px py cx cy b : R) : PFormula :=
  [[ Pr[nrm_inside] = E[ $(nrm_cdf_construct px py cx cy b) ] ]].

Definition nrm_after_add (px py cx cy b : R) : PFormula :=
  subst_bool_pformula nrm_inside nrm_test (nrm_post px py cx cy b).

Definition nrm_after_sample (px py cx cy b : R) : PFormula :=
  subst_real_pformula nrm_d nrm_shift (nrm_after_add px py cx cy b).

Definition nrm_after_assign (px py cx cy b : R) : PFormula :=
  sample_pformula nrm_n (nrm_noise b) (nrm_after_sample px py cx cy b).

Definition nrm_pre (px py cx cy b : R) : PFormula :=
  [[ E[ integral nrm_n ~ $(nrm_noise b),
        indicator[ $(nrm_sqdist px py cx cy) + nrm_n < 1 ] ]
     = E[ integral nrm_n ~ $(nrm_noise b),
          $(nrm_cdf_construct px py cx cy b) ] ]].

Lemma nrm_pre_is_wp :
  forall px py cx cy b : R,
    subst_real_pformula nrm_d (nrm_sqdist px py cx cy)
      (nrm_after_assign px py cx cy b) = nrm_pre px py cx cy b.
Proof. intros; reflexivity. Qed.

(** * Analysis: both sides of the precondition are the same CDF value *)

Lemma nrm_noise_valid :
  forall (b : R) (v : state), 0 < b -> distribution_valid (nrm_noise b) v.
Proof. intros b v Hb; exact Hb. Qed.

Lemma nrm_cdf_construct_value :
  forall (px py cx cy b : R) (v : state),
    0 < b ->
    q_eval (nrm_cdf_construct px py cx cy b) v =
    real_integral (fun z =>
      distribution_density (nrm_noise b) v z *
      real_indicator (z < 1 - nrm_D px py cx cy)).
Proof.
  intros px py cx cy b v Hb.
  unfold nrm_cdf_construct.
  rewrite q_integral_density by (apply nrm_noise_valid; exact Hb).
  apply real_integral_extensional; intro z.
  f_equal.
  rewrite q_eval_indicatorE.
  apply real_indicator_extensional.
  unfold c_lt, update_real, update_real_values.
  cbn [satisfies c_not].
  rewrite nrm_cut_value.
  cbn [term_eval real_program_values].
  unfold nrm_z; rewrite rpv_eq_dec_refl.
  split; intro H; lra.
Qed.

Lemma nrm_density_state_free :
  forall (b z : R) (v w : state),
    distribution_density (nrm_noise b) v z =
    distribution_density (nrm_noise b) w z.
Proof. intros; reflexivity. Qed.

Lemma nrm_pre_valid :
  forall px py cx cy b : R,
    0 < b -> pformula_valid (nrm_pre px py cx cy b).
Proof.
  intros px py cx cy b Hb ps Hadm.
  unfold nrm_pre.
  apply psatisfies_p_eq.
  cbn [pterm_eval].
  apply expectation_extensional; intro v.
  set (c := real_integral (fun z =>
              distribution_density (nrm_noise b) v z *
              real_indicator (z < 1 - nrm_D px py cx cy))).
  rewrite (q_integral_density _ _ _ v) by (apply nrm_noise_valid; exact Hb).
  rewrite (q_integral_density nrm_n (nrm_noise b)
             (nrm_cdf_construct px py cx cy b) v)
    by (apply nrm_noise_valid; exact Hb).
  transitivity c.
  - unfold c; apply real_integral_extensional; intro z.
    f_equal.
    rewrite q_eval_indicatorE.
    apply real_indicator_extensional.
    unfold c_lt, update_real, update_real_values.
    cbn [satisfies c_not term_eval real_program_values].
    unfold nrm_n; rewrite rpv_eq_dec_refl.
    rewrite nrm_sqdist_value.
    split; intro H; lra.
  - rewrite (real_integral_extensional _
               (fun z => c * distribution_density (nrm_noise b) v z)).
    + rewrite real_integral_scale
        by exact (distribution_density_integrable (nrm_noise_valid b v Hb)).
      rewrite (real_integral_distribution_density (nrm_noise_valid b v Hb)).
      change (c = c * 1); ring.
    + intro z.
      rewrite (nrm_cdf_construct_value px py cx cy b _ Hb).
      unfold c.
      rewrite Rmult_comm; f_equal.
Qed.

(** * The mechanism *)

Lemma nrm_noise_valid_under :
  forall (b : R) (pre : PFormula),
    (0 < b)%R ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (nrm_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intros _.
  refine (p_almost_sure_of_pointwise _ _ ps Hadm).
  intro v.
  unfold nrm_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

Theorem nrm_correct :
  forall (px py cx cy b : R) (eta : PFormula),
    (0 < b)%R ->
    {{ $(eta) }}
      $(nrm_prog px py cx cy b)
    {{ Pr[nrm_inside] = E[ integral nrm_z ~ gaussian(0, b),
                           indicator[ nrm_z < $(nrm_cut px py cx cy) ] ] }}.
Proof.
  intros px py cx cy b eta Hb.
  change (hoare_derivable eta (nrm_prog px py cx cy b) (nrm_post px py cx cy b)).
  unfold nrm_prog.
  eapply HSeq with (eta2 := nrm_after_assign px py cx cy b).
  - eapply HConseq with
      (eta1 := subst_real_pformula nrm_d (nrm_sqdist px py cx cy)
                 (nrm_after_assign px py cx cy b))
      (eta2 := nrm_after_assign px py cx cy b).
    + rewrite nrm_pre_is_wp.
      intros ps Hadm _.
      apply nrm_pre_valid; assumption.
    + apply HRealAssign.
    + intros ps Hadm; cbn [psatisfies]; tauto.
  - eapply HSeq with (eta2 := nrm_after_sample px py cx cy b).
    + apply HRealSample.
      * intros ps Hadm; cbn [psatisfies]; intro H; exact H.
      * apply nrm_noise_valid_under; exact Hb.
    + eapply HSeq with (eta2 := nrm_after_add px py cx cy b).
      * apply HRealAssign.
      * apply HBoolAssign.
Qed.
