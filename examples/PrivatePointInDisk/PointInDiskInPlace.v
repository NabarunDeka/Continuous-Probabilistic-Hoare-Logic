(**
  PointInDiskInPlace.v -- a privacy-preserving test of whether a point lies
  inside the unit-radius circle about a given centre.  PERTURB-IN-PLACE
  variant; see PointInDiskAdditive.v for the additive-noise one, which
  proves the same triple.

  The squared distance is computed EXACTLY, one Laplace draw re-centres that
  single scalar on itself, and the noisy value is compared against the
  radius:

      d      := (px - cx)^2 + (py - cy)^2;
      d      <- sample(Laplace(d, b));      (* location IS the variable *)
      inside := (d < 1)

  THE TRIPLE ([pdi_correct], for [0 < b], writing [D] for the true squared
  distance [(px-cx)^2 + (py-cy)^2]):

      { Pr[tt] = 1 }
          pdi_prog px py cx cy b
      { Pr[inside] = laplace_cdf D b 1 }

  So the mechanism reports "inside" with probability exactly the Laplace CDF
  at the radius, centred on the true squared distance.  Accuracy therefore
  degrades smoothly with |D - 1|: a point far inside or far outside is
  classified correctly with probability near 1, one on the boundary with
  probability 1/2.

  WHY THE SQUARED DISTANCE, AND WHY A SINGLE SCALAR.

  [Term] is a pure polynomial algebra ([TProgVar | TLogicVar | TConst |
  TAdd | TMul]) with no square root, so the true Euclidean distance is not
  expressible at all.  The SQUARED distance is, and since the radius is 1 no
  information is lost: [sqrt D <= 1  <->  D <= 1].

  Perturbing the four coordinates separately and then testing membership
  exactly -- the other natural reading of this problem -- is expressible but
  its probability is NOT derivable here.  Solving the disk for one
  coordinate gives section endpoints [cy' +/- sqrt (1 - (x'-cx')^2)], and
  the reachable class is accept regions whose sections are intervals with
  POLYNOMIAL endpoints.  That is the same obstruction that rules out
  Marsaglia's polar method (see UniformConstructions/TriangularRejection.v).
  Closing it would need a four-fold nested Laplace integral over a disk as a
  new axiom, far worse than [real_integral_unit_square_quarter_disk].  See
  flags/FLAGS.md F14.

  WHAT IS NEW HERE.  Two firsts for this directory:

    - the first POLYNOMIAL real assignment, [d := (px-cx)^2 + (py-cy)^2];
    - the first distribution whose LOCATION is a program term rather than a
      constant, [Laplace (TProgVar d) (TConst b)].

  The two interact in exactly the way the calculus wants.  The weakest
  precondition of the sample mentions [d] in the noise location, so the
  integral's value depends on the incoming state.  The assignment's
  substitution then replaces that occurrence by the CLOSED squared-distance
  term, leaving the location state-independent -- which is what makes the
  expectation a constant and the triple provable from [Pr[tt] = 1] alone.
  Substituting into a [QIntegral] touches the distribution but not the bound
  variable, so the indicator's [d] stays bound; that is the whole trick.

  A NOTE ON THE PREDICATE.  The test is the strict [d < 1] rather than
  [d <= 1], because CPHL.v supplies a strict-CDF closed form
  ([laplace_integral_strict_cdf]) and no closed one.  Under continuous noise
  [Pr[d = 1] = 0], so the two agree; the closed version is blocked only by
  the missing law recorded as flags/FLAGS.md F6.

  A NOTE ON PRIVACY.  This file proves the OUTPUT PROBABILITY, not a
  differential-privacy bound.  Two things would be needed for the latter and
  neither is here: a sensitivity bound on the squared distance (which is
  unbounded on an unbounded domain, so the domain must be clamped before any
  fixed [b] is epsilon-DP), and a statement of which operand -- the point or
  the centre -- is the private one.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import HalfLaplaceRejection.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program

    The four coordinates enter as Rocq reals, so [pdi_sqdist] is a CLOSED
    term: that is what makes the perturbed location state-independent after
    the assignment's substitution. *)

Definition pdi_d : RealProgramVar := real_program_var "pdi_d".
Definition pdi_inside : BoolProgramVar := bool_program_var "pdi_inside".

Definition pdi_minus_one : Term := TConst (-1).

Definition pdi_delta (u w : R) : Term := <{ $(u) + $(pdi_minus_one) * $(w) }>.

Definition pdi_sqdist (px py cx cy : R) : Term :=
  <{ ($(pdi_delta px cx) * $(pdi_delta px cx))
     + ($(pdi_delta py cy) * $(pdi_delta py cy)) }>.

(** The true squared distance, as a real. *)
Definition pdi_D (px py cx cy : R) : R :=
  ((px - cx) * (px - cx) + (py - cy) * (py - cy))%R.

Definition pdi_noise (b : R) : Distribution := <{ laplace(pdi_d, b) }>.

Definition pdi_test : CFormula := <{ pdi_d < 1 }>.

Definition pdi_prog (px py cx cy b : R) : Cmd :=
  <{ pdi_d      := $(pdi_sqdist px py cx cy);
     pdi_d      sample $(pdi_noise b);
     pdi_inside b= $(pdi_test) }>.

(** * The squared distance evaluates to [pdi_D] in every state *)

Lemma pdi_sqdist_value :
  forall (px py cx cy : R) (v : state),
    term_eval (pdi_sqdist px py cx cy) v = pdi_D px py cx cy.
Proof.
  intros px py cx cy v.
  unfold pdi_sqdist, pdi_delta, pdi_minus_one, pdi_D.
  cbn [term_eval]; ring.
Qed.

(** * The single integral produced by the sample

    The noise location is the closed squared-distance term, so this is a
    plain Laplace CDF and does not depend on [v]. *)

Lemma pdi_integral :
  forall (px py cx cy b : R) (v : state),
    (0 < b)%R ->
    q_eval
      [[ integral pdi_d ~ $(Laplace (pdi_sqdist px py cx cy) (TConst b)),
         indicator[$(pdi_test)] ]] v
    = laplace_cdf (pdi_D px py cx cy) b 1.
Proof.
  intros px py cx cy b v Hb.
  cbn [q_eval distribution_density].
  rewrite (real_integral_extensional
             _ (fun z =>
                  ((1 / (2 * b)) *
                   exp (- Rabs (z - pdi_D px py cx cy) / b)) *
                  real_indicator (z < 1)%R)).
  - apply laplace_integral_strict_cdf; exact Hb.
  - intro z.
    unfold pdi_test, c_lt, update_real, update_real_values.
    cbn [q_eval satisfies c_not term_eval real_program_values].
    rewrite rpv_eq_dec_refl.
    rewrite pdi_sqdist_value.
    rewrite (real_indicator_extensional _ (z < 1)%R) by lra.
    cbn [term_eval]; ring.
Qed.

(** * The weakest precondition, and that it really is the weakest one *)

Definition pdi_post (px py cx cy b : R) : PFormula :=
  [[ Pr[pdi_inside] = $(laplace_cdf (pdi_D px py cx cy) b 1) ]].

Definition pdi_after_sample (px py cx cy b : R) : PFormula :=
  subst_bool_pformula pdi_inside pdi_test (pdi_post px py cx cy b).

Definition pdi_after_assign (px py cx cy b : R) : PFormula :=
  sample_pformula pdi_d (pdi_noise b) (pdi_after_sample px py cx cy b).

Definition pdi_pre (px py cx cy b : R) : PFormula :=
  [[ E[ integral pdi_d ~ $(Laplace (pdi_sqdist px py cx cy) (TConst b)),
        indicator[ $(pdi_test) ] ]
     = $(laplace_cdf (pdi_D px py cx cy) b 1) ]].

(** The assignment's substitution rewrites the noise LOCATION and leaves the
    integral's bound variable untouched.  Definitional, hence [reflexivity]. *)
Lemma pdi_pre_is_wp :
  forall px py cx cy b : R,
    subst_real_pformula pdi_d (pdi_sqdist px py cx cy)
      (pdi_after_assign px py cx cy b) = pdi_pre px py cx cy b.
Proof. intros; reflexivity. Qed.

(** Total mass one already discharges it, because [pdi_integral] is a
    constant. *)
Lemma pdi_normalized_implies_pre :
  forall px py cx cy b : R,
    (0 < b)%R ->
    pformula_valid [[ Pr[true] = 1 -> $(pdi_pre px py cx cy b) ]].
Proof.
  intros px py cx cy b Hb ps Hadm.
  cbn [psatisfies]; intro Hpre.
  apply psatisfies_p_eq in Hpre.
  cbn [pterm_eval] in Hpre.
  unfold pdi_pre.
  apply psatisfies_p_eq.
  cbn [pterm_eval].
  apply t3_expect_const.
  - exact Hpre.
  - intro v; apply pdi_integral; exact Hb.
Qed.

Lemma pdi_noise_valid_under :
  forall (b : R) (pre : PFormula),
    (0 < b)%R ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (pdi_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intro Hignore.
  clear Hignore; revert ps.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold pdi_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The mechanism *)

Theorem pdi_correct :
  forall px py cx cy b : R,
    (0 < b)%R ->
    {{ Pr[true] = 1 }}
      $(pdi_prog px py cx cy b)
    {{ Pr[pdi_inside] = $(laplace_cdf (pdi_D px py cx cy) b 1) }}.
Proof.
  intros px py cx cy b Hb.
  unfold pdi_prog.
  eapply HSeq with (eta2 := pdi_after_assign px py cx cy b).
  - eapply HConseq with
      (eta1 := subst_real_pformula pdi_d (pdi_sqdist px py cx cy)
                 (pdi_after_assign px py cx cy b))
      (eta2 := pdi_after_assign px py cx cy b).
    + rewrite pdi_pre_is_wp.
      apply pdi_normalized_implies_pre; exact Hb.
    + apply HRealAssign.
    + intro ps; cbn [psatisfies]; tauto.
  - eapply HSeq with (eta2 := pdi_after_sample px py cx cy b).
    + apply HRealSample.
      * intro ps; cbn [psatisfies]; intro H; exact H.
      * apply pdi_noise_valid_under; exact Hb.
    + apply HBoolAssign.
Qed.
