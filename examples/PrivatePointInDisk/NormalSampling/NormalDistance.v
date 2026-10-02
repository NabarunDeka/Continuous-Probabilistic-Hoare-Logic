(**
  NormalDistance.v -- the point-in-disk test with NORMAL noise applied to
  the scalar squared DISTANCE.  The Gaussian counterpart of
  ../PointInDiskAdditive.v, and the companion to NormalDisk.v, which
  perturbs the four coordinates instead.

      d      := (px - cx)^2 + (py - cy)^2;
      n      <- sample(Gaussian(0, b));
      d      := d + n;
      inside := (d < 1)

  THE TRIPLE ([nrm_correct], for [0 < b], writing [D] for the true squared
  distance [(px-cx)^2 + (py-cy)^2]):

      { Pr[tt] = 1 }
          nrm_prog px py cx cy b
      { Pr[inside] = nrm_cdf b (1 - D) }

  UNCONDITIONAL, and with NO added axiom -- not even the Gauss integral that
  GaussianDifference.v needs.  Contrast NormalDisk.v, whose triple is
  conditional on a value nobody can supply.

  WHAT [nrm_cdf] IS, AND WHY IT IS A DEFINITION RATHER THAN A FORMULA.

      nrm_cdf b c  =  INT  phi_{0,b}(z) * 1[z < c]  dz

  the centred normal CDF.  For Laplace, CPHL.v can do better: [laplace_cdf]
  is an elementary FORMULA and [laplace_integral_strict_cdf] evaluates the
  corresponding integral to it.  The normal CDF is [erf], which is not
  elementary, so there is no formula to name -- the honest move is to define
  the function AS the integral and prove the program computes it.

  That is why the postcondition is stated at the cutoff [1 - D] rather than
  the more natural "[nrm_cdf] at [1], centred on [D]".  Re-centring is a
  TRANSLATION of the integration variable, which [real_integral] does not
  support (flags/FLAGS.md F15).  Keeping the noise centred at [0] and moving
  the cutoff instead needs only a pointwise rewrite of the indicator, which
  is available.  The two readings agree: [Pr[D + n < 1] = Pr[n < 1 - D]].

  WHERE THIS SITS.  Collecting the four mechanisms in this directory tree:

      noise on the DISTANCE, Laplace  ../PointInDiskAdditive.v   PROVED,
                                      answer elementary ([laplace_cdf])
      noise on the DISTANCE, normal   this file                  PROVED,
                                      answer defined as an integral
      noise on the POINTS,   Laplace  ../TODO/FourNoiseDisk.v    open
      noise on the POINTS,   normal   NormalDisk.v               open

  So collapsing to a scalar before adding noise is what makes a mechanism
  reachable, for either distribution.  Changing the distribution only
  changes how informative the answer is.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import HalfLaplaceRejection.
Require Import GaussianDifference.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The centred normal CDF, defined as its integral *)

Definition nrm_cdf (b c : R) : R :=
  real_integral (fun z => gc_density 0 b z * real_indicator (z < c)%R).

(** * The program

    The four coordinates are Rocq reals, so the squared distance is a CLOSED
    term and the opening assignment makes the integral state-independent --
    the same device as ../PointInDiskAdditive.v. *)

Definition nrm_d : RealProgramVar := real_program_var "nrm_d".
Definition nrm_n : RealProgramVar := real_program_var "nrm_n".
Definition nrm_inside : BoolProgramVar := bool_program_var "nrm_inside".

Definition nrm_minus_one : Term := TConst (-1).

Definition nrm_delta (u w : R) : Term := <{ $(u) + $(nrm_minus_one) * $(w) }>.

Definition nrm_sqdist (px py cx cy : R) : Term :=
  <{ ($(nrm_delta px cx) * $(nrm_delta px cx))
     + ($(nrm_delta py cy) * $(nrm_delta py cy)) }>.

Definition nrm_D (px py cx cy : R) : R :=
  ((px - cx) * (px - cx) + (py - cy) * (py - cy))%R.

Definition nrm_noise (b : R) : Distribution := <{ gaussian(0, b) }>.

Definition nrm_shift : Term := <{ nrm_d + nrm_n }>.

Definition nrm_test : CFormula := <{ nrm_d < 1 }>.

Definition nrm_prog (px py cx cy b : R) : Cmd :=
  <{ nrm_d      := $(nrm_sqdist px py cx cy);
     nrm_n      sample $(nrm_noise b);
     nrm_d      := $(nrm_shift);
     nrm_inside b= $(nrm_test) }>.

(** * The squared distance evaluates to [nrm_D] in every state *)

Lemma nrm_sqdist_value :
  forall (px py cx cy : R) (v : state),
    term_eval (nrm_sqdist px py cx cy) v = nrm_D px py cx cy.
Proof.
  intros px py cx cy v.
  unfold nrm_sqdist, nrm_delta, nrm_minus_one, nrm_D.
  cbn [term_eval]; ring.
Qed.

(** * The single integral produced by the sample

    The noise is centred at [0] and the opening assignment has closed the
    guard, so this is the centred CDF at the shifted cutoff. *)

Lemma nrm_integral :
  forall (px py cx cy b : R) (v : state),
    (0 < b)%R ->
    q_eval
      [[ integral nrm_n ~ $(Gaussian (TConst 0) (TConst b)),
         indicator[ $(nrm_sqdist px py cx cy) + nrm_n < 1 ] ]] v =
    nrm_cdf b (1 - nrm_D px py cx cy).
Proof.
  intros px py cx cy b v Hb.
  unfold nrm_cdf.
  cbn [q_eval].
  apply real_integral_extensional; intro z.
  f_equal.
  apply real_indicator_extensional.
  unfold nrm_test, c_lt, update_real, update_real_values.
  cbn [satisfies c_not term_eval real_program_values].
  rewrite rpv_eq_dec_refl.
  rewrite nrm_sqdist_value.
  split.
  - intro H; lra.
  - intros H Hc; lra.
Qed.

(** * The weakest precondition *)

Definition nrm_post (px py cx cy b : R) : PFormula :=
  [[ Pr[nrm_inside] = $(nrm_cdf b (1 - nrm_D px py cx cy)) ]].

Definition nrm_after_add (px py cx cy b : R) : PFormula :=
  subst_bool_pformula nrm_inside nrm_test (nrm_post px py cx cy b).

Definition nrm_after_sample (px py cx cy b : R) : PFormula :=
  subst_real_pformula nrm_d nrm_shift (nrm_after_add px py cx cy b).

Definition nrm_after_assign (px py cx cy b : R) : PFormula :=
  sample_pformula nrm_n (nrm_noise b) (nrm_after_sample px py cx cy b).

Definition nrm_pre (px py cx cy b : R) : PFormula :=
  [[ E[ integral nrm_n ~ $(Gaussian (TConst 0) (TConst b)),
        indicator[ $(nrm_sqdist px py cx cy) + nrm_n < 1 ] ]
     = $(nrm_cdf b (1 - nrm_D px py cx cy)) ]].

(** The opening assignment closes the guard; [nrm_n] stays bound. *)
Lemma nrm_pre_is_wp :
  forall px py cx cy b : R,
    subst_real_pformula nrm_d (nrm_sqdist px py cx cy)
      (nrm_after_assign px py cx cy b) = nrm_pre px py cx cy b.
Proof. intros; reflexivity. Qed.

Lemma nrm_normalized_implies_pre :
  forall px py cx cy b : R,
    (0 < b)%R ->
    pformula_valid [[ Pr[true] = 1 -> $(nrm_pre px py cx cy b) ]].
Proof.
  intros px py cx cy b Hb ps Hadm.
  cbn [psatisfies]; intro Hnorm.
  apply psatisfies_p_eq in Hnorm.
  cbn [pterm_eval] in Hnorm.
  unfold nrm_pre.
  apply psatisfies_p_eq.
  cbn [pterm_eval].
  apply t3_expect_const.
  - exact Hnorm.
  - intro v; apply nrm_integral; exact Hb.
Qed.

Lemma nrm_noise_valid_under :
  forall (b : R) (pre : PFormula),
    (0 < b)%R ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (nrm_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intro Hignore.
  clear Hignore; revert ps.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold nrm_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The mechanism *)

Theorem nrm_correct :
  forall px py cx cy b : R,
    (0 < b)%R ->
    {{ Pr[true] = 1 }}
      $(nrm_prog px py cx cy b)
    {{ Pr[nrm_inside] = $(nrm_cdf b (1 - nrm_D px py cx cy)) }}.
Proof.
  intros px py cx cy b Hb.
  unfold nrm_prog.
  eapply HSeq with (eta2 := nrm_after_assign px py cx cy b).
  - eapply HConseq with
      (eta1 := subst_real_pformula nrm_d (nrm_sqdist px py cx cy)
                 (nrm_after_assign px py cx cy b))
      (eta2 := nrm_after_assign px py cx cy b).
    + rewrite nrm_pre_is_wp.
      apply nrm_normalized_implies_pre; exact Hb.
    + apply HRealAssign.
    + intro ps; cbn [psatisfies]; tauto.
  - eapply HSeq with (eta2 := nrm_after_sample px py cx cy b).
    + apply HRealSample.
      * intro ps; cbn [psatisfies]; intro H; exact H.
      * apply nrm_noise_valid_under; exact Hb.
    + eapply HSeq with (eta2 := nrm_after_add px py cx cy b).
      * apply HRealAssign.
      * apply HBoolAssign.
Qed.
