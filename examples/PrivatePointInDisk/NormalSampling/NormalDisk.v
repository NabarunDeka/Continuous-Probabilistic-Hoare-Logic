(**
  NormalDisk.v -- the four-noise point-in-disk mechanism with NORMAL noise
  instead of Laplace, and what the closure of the normal family under
  differences does and does not buy.

      n1 <- sample(Gaussian(0, b));   (* on px *)
      n3 <- sample(Gaussian(0, b));   (* on cx *)
      n2 <- sample(Gaussian(0, b));   (* on py *)
      n4 <- sample(Gaussian(0, b));   (* on cy *)
      inside := ( ((px+n1) - (cx+n3))^2 + ((py+n2) - (cy+n4))^2 < 1 )

  THE TRIPLE ([nd_four_noise_derivable], for [0 < b]).  It is CONDITIONAL:
  the value of the four-fold integral is a hypothesis, not a conclusion.

      (forall v, q_eval (nd_construct px py cx cy b) v = r)
        ->
      { Pr[tt] = 1 }
          nd_prog px py cx cy b
      { Pr[inside] = r }

  Read it as: every Hoare step of this mechanism is available -- the four
  [HRealSample]s, the [HBoolAssign], the [HSeq] chain -- and the ONLY thing
  standing between it and an unconditional triple is the value of that one
  integral.  The hypothesis is exactly the open part, and the two ways to
  discharge it are the targets at the end of the file
  ([nd_reduction_target], [nd_central_target]).

  WHAT IS PROVED HERE

  - [nd_combined_noise] : the two noises acting on one coordinate collapse
    into a SINGLE normal.  Each difference n1 - n3 has density
    [Gaussian(0, b*sqrt 2)], by GaussianDifference.v's [gc_difference].
    This is the "cut out integrals" step, at the analytic level, and unlike
    the Laplace case the result stays inside the sampling family -- there is
    a [Distribution] in CPHL denoting it.

  - [nd_four_noise_derivable] : the Hoare derivation of the whole triple
    goes through given only the VALUE of the integral.  No new axioms.  So
    the Hoare logic is not what blocks this.

  WHAT IS NOT, AND THE PAYOFF THAT NORMALS DO GIVE

  - [nd_reduction_target] : that the four-fold weakest precondition equals
    the two-fold one.  Blocked by flags/FLAGS.md F15 -- collapsing nested
    integrals needs change of variables and Fubini, which [real_integral]
    lacks.  Note this is blocked for exactly the same reason as in the
    Laplace case: switching distribution does not help the REDUCTION.

  - [nd_central_target] : where normals genuinely win.  At the centre
    (px = cx and py = cy) the answer is ELEMENTARY:

        Pr[inside]  =  1 - exp( -1 / (4 b^2) ).

    Reason: n1-n3 and n2-n4 are independent N(0, sigma) with
    sigma^2 = 2 b^2, so the pair is a rotationally symmetric bivariate
    normal, and the squared radius is exponential:
    Pr[U^2+V^2 < 1] = 1 - exp(-1/(2 sigma^2)) = 1 - exp(-1/(4 b^2)).
    Checked numerically against a 3e6-sample Monte Carlo:

        b = 0.3   MC 0.93780   formula 0.93782
        b = 0.5   MC 0.63214   formula 0.63212
        b = 1.0   MC 0.22107   formula 0.22120

    The Laplace analogue has no such closed form at ANY offset -- see
    ../TODO/FourNoiseDisk.v.  Still, [nd_central_target] is NOT proved
    here: reaching it from iterated one-dimensional integrals needs POLAR
    COORDINATES, a two-dimensional change of variables, which is a strictly
    stronger missing law than the one-dimensional ones F15 asks for.

  - Off the centre the value is a Marcum Q-function (equivalently a
    noncentral chi-squared CDF with two degrees of freedom), which is not
    elementary.  So the normal gain is confined to the symmetric case.

  THE TRADE, STATED PLAINLY.  Compared with Laplace, normal noise is

      BETTER in 2-D : the central disk probability has a closed form at all,
                      because the bivariate normal is rotationally
                      symmetric;
      WORSE  in 1-D : the Laplace CDF is elementary and CPHL evaluates it
                      ([laplace_integral_strict_cdf]), so the 1-D membership
                      tests in ../OneDimensional/ close completely.  The
                      normal CDF is erf, which CPHL has no law for and which
                      is not elementary -- so the normal 1-D test is out of
                      reach even though the Laplace one is routine.

  Neither change removes the F15 obstruction to the 4 -> 2 reduction.
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

(** * Cutting two noises down to one

    The difference of the two normals acting on a coordinate is itself
    normal, with deviation [b * sqrt 2]. *)

Lemma nd_sqrt_two :
  forall b : R, (0 < b)%R -> sqrt (b * b + b * b) = (b * sqrt 2)%R.
Proof.
  intros b Hb.
  replace (b * b + b * b)%R with (2 * (b * b))%R by ring.
  assert (H2 : (0 <= 2)%R) by lra.
  assert (Hbb : (0 <= b * b)%R) by nra.
  rewrite (sqrt_mult 2 (b * b) H2 Hbb).
  rewrite (sqrt_square b) by lra.
  ring.
Qed.

Theorem nd_combined_noise :
  forall b z : R,
    (0 < b)%R ->
    real_integral (fun u => gc_density 0 b u * gc_density 0 b (u - z)) =
    gc_density 0 (b * sqrt 2) z.
Proof.
  intros b z Hb.
  rewrite (gc_difference_sqrt 0 b 0 b z Hb Hb).
  rewrite (nd_sqrt_two b Hb).
  f_equal; ring.
Qed.

(** The combined noise is itself a CPHL distribution -- which is the sense in
    which the normal family is closed and the Laplace family is not. *)
Definition nd_combined (b : R) : Distribution := <{ gaussian(0, $(b * sqrt 2)) }>.

Lemma nd_combined_density :
  forall (b z : R) (v : state),
    distribution_density (nd_combined b) v z = gc_density 0 (b * sqrt 2) z.
Proof. intros; reflexivity. Qed.

(** * The program *)

Definition nd_n1 : RealProgramVar := real_program_var "nd_n1".
Definition nd_n3 : RealProgramVar := real_program_var "nd_n3".
Definition nd_n2 : RealProgramVar := real_program_var "nd_n2".
Definition nd_n4 : RealProgramVar := real_program_var "nd_n4".
Definition nd_inside : BoolProgramVar := bool_program_var "nd_inside".

Definition nd_minus_one : Term := TConst (-1).

Definition nd_noise (b : R) : Distribution := <{ gaussian(0, b) }>.

Definition nd_dx (px cx : R) : Term :=
  <{ ($(px) + nd_n1) + $(nd_minus_one) * ($(cx) + nd_n3) }>.
Definition nd_dy (py cy : R) : Term :=
  <{ ($(py) + nd_n2) + $(nd_minus_one) * ($(cy) + nd_n4) }>.

Definition nd_disk (px py cx cy : R) : CFormula :=
  <{ ($(nd_dx px cx) * $(nd_dx px cx))
     + ($(nd_dy py cy) * $(nd_dy py cy)) < 1 }>.

Definition nd_prog (px py cx cy b : R) : Cmd :=
  <{ nd_n1 sample $(nd_noise b);
     nd_n3 sample $(nd_noise b);
     nd_n2 sample $(nd_noise b);
     nd_n4 sample $(nd_noise b);
     nd_inside b= $(nd_disk px py cx cy) }>.

(** The four-fold weakest precondition.  The assertion logic expresses it. *)
Definition nd_construct (px py cx cy b : R) : PConstruct :=
  [[ integral nd_n1 ~ $(nd_noise b),
     integral nd_n3 ~ $(nd_noise b),
     integral nd_n2 ~ $(nd_noise b),
     integral nd_n4 ~ $(nd_noise b),
     indicator[ $(nd_disk px py cx cy) ] ]].

(** The two-fold one, after the combination [nd_combined_noise] licenses. *)
Definition nd_two_construct (px py cx cy b : R) : PConstruct :=
  [[ integral nd_n1 ~ $(nd_combined b),
     integral nd_n2 ~ $(nd_combined b),
     indicator[ (($(px) + $(nd_minus_one) * $(cx)) + nd_n1)
                * (($(px) + $(nd_minus_one) * $(cx)) + nd_n1)
                + (($(py) + $(nd_minus_one) * $(cy)) + nd_n2)
                  * (($(py) + $(nd_minus_one) * $(cy)) + nd_n2) < 1 ] ]].

(** * The Hoare derivation, modulo the integral *)

Definition nd_post (r : R) : PFormula := [[ Pr[nd_inside] = $(r) ]].

Definition nd_s3 (px py cx cy r : R) : PFormula :=
  subst_bool_pformula nd_inside (nd_disk px py cx cy) (nd_post r).
Definition nd_s2 (px py cx cy b r : R) : PFormula :=
  sample_pformula nd_n4 (nd_noise b) (nd_s3 px py cx cy r).
Definition nd_s1 (px py cx cy b r : R) : PFormula :=
  sample_pformula nd_n2 (nd_noise b) (nd_s2 px py cx cy b r).
Definition nd_s0 (px py cx cy b r : R) : PFormula :=
  sample_pformula nd_n3 (nd_noise b) (nd_s1 px py cx cy b r).
Definition nd_pre (px py cx cy b r : R) : PFormula :=
  sample_pformula nd_n1 (nd_noise b) (nd_s0 px py cx cy b r).

Lemma nd_pre_shape :
  forall px py cx cy b r : R,
    nd_pre px py cx cy b r = [[ E[ $(nd_construct px py cx cy b) ] = $(r) ]].
Proof. intros; reflexivity. Qed.

Lemma nd_noise_valid_under :
  forall (b : R) (pre : PFormula),
    (0 < b)%R ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (nd_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intro Hignore.
  clear Hignore; revert ps.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold nd_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** Given only the value of the integral, every rule application succeeds. *)
Theorem nd_four_noise_derivable :
  forall px py cx cy b r : R,
    (0 < b)%R ->
    (forall v : state, q_eval (nd_construct px py cx cy b) v = r) ->
    {{ Pr[true] = 1 }}
      $(nd_prog px py cx cy b)
    {{ Pr[nd_inside] = $(r) }}.
Proof.
  intros px py cx cy b r Hb Hval.
  unfold nd_prog.
  eapply HSeq with (eta2 := nd_s0 px py cx cy b r).
  - apply HRealSample.
    + intro ps.
    + intro Hadm.
      cbn [psatisfies]; intro Hnorm.
      apply psatisfies_p_eq in Hnorm.
      cbn [pterm_eval] in Hnorm.
      change (sample_pformula nd_n1 (nd_noise b) (nd_s0 px py cx cy b r))
        with (nd_pre px py cx cy b r).
      rewrite nd_pre_shape.
      apply psatisfies_p_eq.
      cbn [pterm_eval].
      apply t3_expect_const; [exact Hnorm | exact Hval].
    + apply nd_noise_valid_under; exact Hb.
  - eapply HSeq with (eta2 := nd_s1 px py cx cy b r).
    + apply HRealSample.
      * intro ps; cbn [psatisfies]; intro H; exact H.
      * apply nd_noise_valid_under; exact Hb.
    + eapply HSeq with (eta2 := nd_s2 px py cx cy b r).
      * apply HRealSample.
        -- intro ps; cbn [psatisfies]; intro H; exact H.
        -- apply nd_noise_valid_under; exact Hb.
      * eapply HSeq with (eta2 := nd_s3 px py cx cy r).
        -- apply HRealSample.
           ++ intro ps; cbn [psatisfies]; intro H; exact H.
           ++ apply nd_noise_valid_under; exact Hb.
        -- apply HBoolAssign.
Qed.

(** * The two statements that remain open

    Both STATED, neither proved. *)

(** 4 -> 2.  The analytic content is [nd_combined_noise]; what is missing is
    the right to reorganise the nested integrals.  flags/FLAGS.md F15. *)
Definition nd_reduction_target (px py cx cy b : R) : Prop :=
  forall v : state,
    q_eval (nd_construct px py cx cy b) v =
    q_eval (nd_two_construct px py cx cy b) v.

(** The central case, where normal noise has an elementary answer that
    Laplace never does.  Reaching it needs polar coordinates. *)
Definition nd_central_target (p b : R) : Prop :=
  forall v : state,
    q_eval (nd_construct p p p p b) v = (1 - exp (- 1 / (4 * b * b)))%R.
