(**
  PointInDiskAdditive.v -- the same privacy-preserving disk-membership test
  as PointInDiskInPlace.v, written in the idiomatic Laplace-mechanism shape:
  draw centred noise into its OWN variable, then add it.

      d      := (px - cx)^2 + (py - cy)^2;
      n      <- sample(Laplace(0, b));      (* location is the constant 0 *)
      d      := d + n;
      inside := (d < 1)

  THE TRIPLE ([pda_correct], for [0 < b], writing [D] for the true squared
  distance [(px-cx)^2 + (py-cy)^2]):

      { Pr[tt] = 1 }
          pda_prog px py cx cy b
      { Pr[inside] = laplace_cdf D b 1 }

  -- textually the same postcondition as PointInDiskInPlace.v's
  [pdi_correct], so the two programs are proved to have identical output
  distributions.  [pda_agrees_with_in_place] records that.

  WHY BOTH EXIST.  The mechanisms differ only in where the noise is written,
  and the derivations differ only in WHAT the opening assignment closes:

    - in-place: the sample's weakest precondition mentions [d] in the noise
      LOCATION, and [d := sqdist] closes that;
    - here: the location is already the constant [0], and it is the GUARD
      [d + n < 1] inside the indicator that mentions [d]; the same
      [d := sqdist] closes that instead.

  Either way the integral becomes state-independent, which is what makes the
  triple reachable from [Pr[tt] = 1] alone.  This file is the one to extend
  towards a differential-privacy statement: [output = f(x) + Lap(b)] is the
  shape the DP literature uses, and the noise here is a named variable that
  a sensitivity argument can talk about.

  THE ONE EXTRA STEP.  Centred noise puts the answer in the form
  [laplace_cdf 0 b (1 - D)] rather than [laplace_cdf D b 1].  These agree by
  translation invariance ([pda_cdf_shift]); the in-place variant lands on the
  second form directly and needs no such bridge.

  Everything else -- why the squared distance rather than the distance, why
  the strict test, why the coordinates are Rocq reals rather than program
  variables, and why perturbing the four coordinates separately is NOT
  derivable -- is as described in PointInDiskInPlace.v and in
  flags/FLAGS.md F14.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import HalfLaplaceRejection.
Require Import PointInDiskInPlace.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program

    As in PointInDiskInPlace.v the four coordinates are Rocq reals, so
    [pda_sqdist] is a CLOSED term. *)

Definition pda_d : RealProgramVar := real_program_var "pda_d".
Definition pda_n : RealProgramVar := real_program_var "pda_n".
Definition pda_inside : BoolProgramVar := bool_program_var "pda_inside".

Definition pda_minus_one : Term := TConst (-1).

Definition pda_delta (u w : R) : Term := <{ $(u) + $(pda_minus_one) * $(w) }>.

Definition pda_sqdist (px py cx cy : R) : Term :=
  <{ ($(pda_delta px cx) * $(pda_delta px cx))
     + ($(pda_delta py cy) * $(pda_delta py cy)) }>.

Definition pda_D (px py cx cy : R) : R :=
  ((px - cx) * (px - cx) + (py - cy) * (py - cy))%R.

(** Centred noise, in its own variable. *)
Definition pda_noise (b : R) : Distribution := <{ laplace(0, b) }>.

Definition pda_shift : Term := <{ pda_d + pda_n }>.

Definition pda_test : CFormula := <{ pda_d < 1 }>.

Definition pda_prog (px py cx cy b : R) : Cmd :=
  <{ pda_d      := $(pda_sqdist px py cx cy);
     pda_n      sample $(pda_noise b);
     pda_d      := $(pda_shift);
     pda_inside b= $(pda_test) }>.

(** * Translation invariance of the Laplace CDF

    Centred noise answers at cutoff [1 - D] about location [0]; the in-place
    variant answers at cutoff [1] about location [D].  Same number. *)

Lemma pda_cdf_shift :
  forall D b : R, laplace_cdf 0 b (1 - D) = laplace_cdf D b 1.
Proof.
  intros D b.
  unfold laplace_cdf.
  destruct (Rle_dec (1 - D) 0) as [H1 | H1];
    destruct (Rle_dec 1 D) as [H2 | H2].
  - replace (1 - D - 0)%R with (1 - D)%R by ring; reflexivity.
  - exfalso; lra.
  - exfalso; lra.
  - replace (1 - D - 0)%R with (1 - D)%R by ring; reflexivity.
Qed.

(** * The squared distance evaluates to [pda_D] in every state *)

Lemma pda_sqdist_value :
  forall (px py cx cy : R) (v : state),
    term_eval (pda_sqdist px py cx cy) v = pda_D px py cx cy.
Proof.
  intros px py cx cy v.
  unfold pda_sqdist, pda_delta, pda_minus_one, pda_D.
  cbn [term_eval]; ring.
Qed.

(** * The single integral produced by the sample

    The noise location is the constant [0]; it is the GUARD that the opening
    assignment has already closed. *)

Lemma pda_integral :
  forall (px py cx cy b : R) (v : state),
    (0 < b)%R ->
    q_eval
      [[ integral pda_n ~ $(Laplace (TConst 0) (TConst b)),
         indicator[ $(pda_sqdist px py cx cy) + pda_n < 1 ] ]] v
    = laplace_cdf (pda_D px py cx cy) b 1.
Proof.
  intros px py cx cy b v Hb.
  cbn [q_eval distribution_density].
  rewrite (real_integral_extensional
             _ (fun z =>
                  ((1 / (2 * b)) * exp (- Rabs (z - 0) / b)) *
                  real_indicator (z < 1 - pda_D px py cx cy)%R)).
  - rewrite laplace_integral_strict_cdf by exact Hb.
    apply pda_cdf_shift.
  - intro z.
    unfold pda_test, c_lt, update_real, update_real_values.
    cbn [q_eval satisfies c_not term_eval real_program_values].
    rewrite rpv_eq_dec_refl.
    rewrite pda_sqdist_value.
    rewrite (real_indicator_extensional _ (z < 1 - pda_D px py cx cy)%R) by lra.
    cbn [term_eval]; ring.
Qed.

(** * The weakest precondition *)

Definition pda_post (px py cx cy b : R) : PFormula :=
  [[ Pr[pda_inside] = $(laplace_cdf (pda_D px py cx cy) b 1) ]].

Definition pda_after_add (px py cx cy b : R) : PFormula :=
  subst_bool_pformula pda_inside pda_test (pda_post px py cx cy b).

Definition pda_after_sample (px py cx cy b : R) : PFormula :=
  subst_real_pformula pda_d pda_shift (pda_after_add px py cx cy b).

Definition pda_after_assign (px py cx cy b : R) : PFormula :=
  sample_pformula pda_n (pda_noise b) (pda_after_sample px py cx cy b).

Definition pda_pre (px py cx cy b : R) : PFormula :=
  [[ E[ integral pda_n ~ $(Laplace (TConst 0) (TConst b)),
        indicator[ $(pda_sqdist px py cx cy) + pda_n < 1 ] ]
     = $(laplace_cdf (pda_D px py cx cy) b 1) ]].

(** The opening assignment substitutes into the indicator's GUARD; the
    integral's bound variable [pda_n] is untouched.  Definitional. *)
Lemma pda_pre_is_wp :
  forall px py cx cy b : R,
    subst_real_pformula pda_d (pda_sqdist px py cx cy)
      (pda_after_assign px py cx cy b) = pda_pre px py cx cy b.
Proof. intros; reflexivity. Qed.

Lemma pda_normalized_implies_pre :
  forall px py cx cy b : R,
    (0 < b)%R ->
    pformula_valid [[ Pr[true] = 1 -> $(pda_pre px py cx cy b) ]].
Proof.
  intros px py cx cy b Hb ps Hadm.
  cbn [psatisfies]; intro Hpre.
  apply psatisfies_p_eq in Hpre.
  cbn [pterm_eval] in Hpre.
  unfold pda_pre.
  apply psatisfies_p_eq.
  cbn [pterm_eval].
  apply t3_expect_const.
  - exact Hpre.
  - intro v; apply pda_integral; exact Hb.
Qed.

Lemma pda_noise_valid_under :
  forall (b : R) (pre : PFormula),
    (0 < b)%R ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (pda_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intro Hignore.
  clear Hignore; revert ps.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold pda_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The mechanism *)

Theorem pda_correct :
  forall px py cx cy b : R,
    (0 < b)%R ->
    {{ Pr[true] = 1 }}
      $(pda_prog px py cx cy b)
    {{ Pr[pda_inside] = $(laplace_cdf (pda_D px py cx cy) b 1) }}.
Proof.
  intros px py cx cy b Hb.
  unfold pda_prog.
  eapply HSeq with (eta2 := pda_after_assign px py cx cy b).
  - eapply HConseq with
      (eta1 := subst_real_pformula pda_d (pda_sqdist px py cx cy)
                 (pda_after_assign px py cx cy b))
      (eta2 := pda_after_assign px py cx cy b).
    + rewrite pda_pre_is_wp.
      apply pda_normalized_implies_pre; exact Hb.
    + apply HRealAssign.
    + intro ps; cbn [psatisfies]; tauto.
  - eapply HSeq with (eta2 := pda_after_sample px py cx cy b).
    + apply HRealSample.
      * intro ps; cbn [psatisfies]; intro H; exact H.
      * apply pda_noise_valid_under; exact Hb.
    + eapply HSeq with (eta2 := pda_after_add px py cx cy b).
      * apply HRealAssign.
      * apply HBoolAssign.
Qed.

(** * Cross-check against the in-place variant

    Both files define the same squared distance, so [pdi_correct] and
    [pda_correct] assert the same probability for the same inputs: the two
    mechanisms are output-equivalent even though the noise is written
    differently.

    This is a DEFINITIONAL check, not an independent derivation.  Both
    proofs run through [laplace_integral_strict_cdf] and [t3_expect_const],
    so unlike the MaxOfTwoUniforms.v / TriangularRejection.v pair this does
    not cross-validate an axiom -- it only confirms the two programs were
    given the same specification. *)
Lemma pda_agrees_with_in_place :
  forall px py cx cy b : R,
    laplace_cdf (pda_D px py cx cy) b 1
    = laplace_cdf (pdi_D px py cx cy) b 1.
Proof. intros; reflexivity. Qed.
