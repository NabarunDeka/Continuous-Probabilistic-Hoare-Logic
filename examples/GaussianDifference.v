(**
  GaussianDifference.v

  Programs ([gc_two_sample m1 s1 m2 s2], [gc_one_sample m s]):
      gc_x <- sample(gaussian(m1, s1)); gc_y <- sample(gaussian(m2, s2)); gc_d := gc_x + -1 * gc_y
      gc_d <- sample(gaussian(m, s))
  Triple: none proved.  Unproved target [gc_program_target] (equal weakest
  preconditions for the event gc_d < t, with m = m1 - m2 and s * s = s1 * s1 + s2 * s2):
      E[ integral gc_x ~ gaussian(m1, s1), integral gc_y ~ gaussian(m2, s2),
         indicator[gc_x + -1 * gc_y < t] ]
        = E[ integral gc_d ~ gaussian(m1 - m2, s), indicator[gc_d < t] ]
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
Require Import CPHL.
Require Import CPHLFacts.DistributionFacts CPHLFacts.CalculationFacts.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The normal density, matching CPHL.v's [Gaussian] *)

Definition gc_density (m s z : R) : R :=
  ((1 / (s * sqrt (2 * PI))) *
   exp (- ((z - m) * (z - m)) / (2 * s * s)))%R.

Lemma gc_density_is_gaussian :
  forall (m s z : R) (v : state),
    gc_density m s z =
    distribution_density (Gaussian (TConst m) (TConst s)) v z.
Proof. intros; reflexivity. Qed.

(** * The Gauss integral (proved from the normalisation of the Gaussian density)

    Parameterised by the VARIANCE [v], which keeps every square root out of
    the algebra below. *)

Lemma gc_kernel_as_density :
  forall m v u : R,
    (0 < v)%R ->
    exp (- ((u - m) * (u - m)) / (2 * v)) =
    (sqrt v * sqrt (2 * PI) *
     distribution_density (Gaussian (TConst m) (TConst (sqrt v))) demo_valuation u)%R.
Proof.
  intros m v u Hv.
  assert (Hs : (0 < sqrt v)%R) by (apply sqrt_lt_R0; exact Hv).
  assert (Hpi : (0 < sqrt (2 * PI))%R)
    by (apply sqrt_lt_R0; generalize PI_RGT_0; lra).
  unfold distribution_density; cbn [term_eval].
  pattern v at 1; rewrite <- (sqrt_sqrt v) by lra.
  replace (2 * (sqrt v * sqrt v))%R with (2 * sqrt v * sqrt v)%R by ring.
  field; split; lra.
Qed.

Lemma gc_gaussian_valid :
  forall m v : R, (0 < v)%R ->
    distribution_valid (Gaussian (TConst m) (TConst (sqrt v))) demo_valuation.
Proof. intros m v Hv; apply sqrt_lt_R0; exact Hv. Qed.

Lemma real_integrable_gaussian_kernel :
  forall m v : R,
    (0 < v)%R ->
    real_integrable (fun u => exp (- ((u - m) * (u - m)) / (2 * v))).
Proof.
  intros m v Hv.
  apply (real_integrable_ext
           (fun u => sqrt v * sqrt (2 * PI) *
              distribution_density (Gaussian (TConst m) (TConst (sqrt v)))
                demo_valuation u)%R).
  - intro u; symmetry; apply gc_kernel_as_density; exact Hv.
  - apply real_integrable_scale.
    exact (distribution_density_integrable (gc_gaussian_valid m v Hv)).
Qed.

Lemma real_integral_gaussian_kernel :
  forall m v : R,
    (0 < v)%R ->
    real_integral (fun u => exp (- ((u - m) * (u - m)) / (2 * v))) =
    sqrt (2 * PI * v).
Proof.
  intros m v Hv.
  rewrite (real_integral_extensional _
             (fun u => sqrt v * sqrt (2 * PI) *
                distribution_density (Gaussian (TConst m) (TConst (sqrt v)))
                  demo_valuation u)%R)
    by (intro u; apply gc_kernel_as_density; exact Hv).
  rewrite real_integral_scale
    by exact (distribution_density_integrable (gc_gaussian_valid m v Hv)).
  rewrite (real_integral_distribution_density (gc_gaussian_valid m v Hv)).
  rewrite (sqrt_mult_alt (2 * PI) v) by (generalize PI_RGT_0; lra).
  change (sqrt v * sqrt (2 * PI) * 1 = sqrt (2 * PI) * sqrt v)%R; ring.
Qed.

(** * Two small facts *)

Lemma gc_sumsq_pos :
  forall s1 s2 : R,
    (0 < s1)%R -> (0 < s2)%R -> (0 < s1 * s1 + s2 * s2)%R.
Proof.
  intros s1 s2 H1 H2.
  apply Rplus_lt_0_compat; apply Rmult_lt_0_compat; assumption.
Qed.

Lemma gc_pair :
  forall c1 c2 A B : R,
    ((c1 * exp A) * (c2 * exp B))%R = ((c1 * c2) * exp (A + B))%R.
Proof. intros; rewrite exp_plus; ring. Qed.

Lemma gc_sqrt_var :
  forall s1 s2 s : R,
    (0 < s1)%R -> (0 < s2)%R -> (0 < s)%R ->
    sqrt (2 * PI * (s1 * s1 * (s2 * s2) / (s * s))) =
    (sqrt (2 * PI) * (s1 * s2) / s)%R.
Proof.
  intros s1 s2 s H1 H2 Hs.
  assert (Hq : (0 <= s1 * s2 / s)%R).
  { apply Rle_mult_inv_pos; [| exact Hs].
    left; apply Rmult_lt_0_compat; assumption. }
  replace (2 * PI * (s1 * s1 * (s2 * s2) / (s * s)))%R
    with ((2 * PI) * ((s1 * s2 / s) * (s1 * s2 / s)))%R
    by (field; lra).
  rewrite sqrt_mult_alt by (generalize PI_RGT_0; lra).
  rewrite sqrt_square by exact Hq.
  field; lra.
Qed.

(** * Completing the square

    Pure field identity: no square roots, no [s]. *)

Lemma gc_exponent_identity :
  forall m1 s1 m2 s2 z u : R,
    (0 < s1)%R -> (0 < s2)%R ->
    (- ((u - m1) * (u - m1)) / (2 * s1 * s1)
     + - ((z - u - m2) * (z - u - m2)) / (2 * s2 * s2))%R =
    (- ((z - (m1 + m2)) * (z - (m1 + m2))) / (2 * (s1 * s1 + s2 * s2))
     + - ((u - (m1 + (z - m2 - m1) * (s1 * s1) / (s1 * s1 + s2 * s2)))
          * (u - (m1 + (z - m2 - m1) * (s1 * s1) / (s1 * s1 + s2 * s2))))
       / (2 * (s1 * s1 * (s2 * s2) / (s1 * s1 + s2 * s2))))%R.
Proof.
  intros m1 s1 m2 s2 z u H1 H2.
  assert (Hs1 : (s1 <> 0)%R) by lra.
  assert (Hs2 : (s2 <> 0)%R) by lra.
  assert (HSpos : (0 < s1 * s1 + s2 * s2)%R) by (apply gc_sumsq_pos; assumption).
  assert (HS : (s1 * s1 + s2 * s2 <> 0)%R) by (apply Rgt_not_eq; exact HSpos).
  field; repeat split; assumption.
Qed.

(** * THE CONVOLUTION: the normal family is closed under sums *)

Theorem gc_convolution :
  forall m1 s1 m2 s2 s z : R,
    (0 < s1)%R -> (0 < s2)%R -> (0 < s)%R ->
    (s * s = s1 * s1 + s2 * s2)%R ->
    real_integral (fun u => gc_density m1 s1 u * gc_density m2 s2 (z - u)) =
    gc_density (m1 + m2) s z.
Proof.
  intros m1 s1 m2 s2 s z H1 H2 Hs Hvar.
  assert (Hs1 : (s1 <> 0)%R) by lra.
  assert (Hs2 : (s2 <> 0)%R) by lra.
  assert (Hs0 : (s <> 0)%R) by lra.
  assert (Hpi : (0 < sqrt (2 * PI))%R)
    by (apply sqrt_lt_R0; generalize PI_RGT_0; lra).
  assert (Hss : (0 < s * s)%R) by (apply Rmult_lt_0_compat; assumption).
  assert (Hvr : (0 < s1 * s1 * (s2 * s2) / (s * s))%R).
  { apply Rdiv_lt_0_compat; [| exact Hss].
    apply Rmult_lt_0_compat; apply Rmult_lt_0_compat; assumption. }
  rewrite (real_integral_extensional
             _ (fun u =>
                  ((1 / (s1 * sqrt (2 * PI))) * (1 / (s2 * sqrt (2 * PI)))
                   * exp (- ((z - (m1 + m2)) * (z - (m1 + m2)))
                          / (2 * s * s)))
                  * exp (- ((u - (m1 + (z - m2 - m1) * (s1 * s1) / (s * s)))
                            * (u - (m1 + (z - m2 - m1) * (s1 * s1) / (s * s))))
                         / (2 * (s1 * s1 * (s2 * s2) / (s * s)))))).
  - rewrite real_integral_scale
      by (apply real_integrable_gaussian_kernel; exact Hvr).
    rewrite (real_integral_gaussian_kernel
               (m1 + (z - m2 - m1) * (s1 * s1) / (s * s))
               (s1 * s1 * (s2 * s2) / (s * s)) Hvr).
    rewrite (gc_sqrt_var s1 s2 s H1 H2 Hs).
    unfold gc_density.
    field; repeat split; lra.
  - intro u.
    unfold gc_density.
    rewrite gc_pair.
    rewrite (gc_exponent_identity m1 s1 m2 s2 z u H1 H2).
    rewrite <- Hvar.
    replace (2 * (s * s))%R with (2 * s * s)%R by ring.
    rewrite exp_plus.
    ring.
Qed.

(** * THE DIFFERENCE: what the file is named for *)

Theorem gc_difference :
  forall m1 s1 m2 s2 s z : R,
    (0 < s1)%R -> (0 < s2)%R -> (0 < s)%R ->
    (s * s = s1 * s1 + s2 * s2)%R ->
    real_integral (fun u => gc_density m1 s1 u * gc_density m2 s2 (u - z)) =
    gc_density (m1 - m2) s z.
Proof.
  intros m1 s1 m2 s2 s z H1 H2 Hs Hvar.
  transitivity
    (real_integral (fun u => gc_density m1 s1 u * gc_density (- m2) s2 (z - u))).
  - apply real_integral_extensional; intro u.
    f_equal.
    unfold gc_density.
    f_equal; f_equal; field; lra.
  - rewrite (gc_convolution m1 s1 (- m2) s2 s z H1 H2 Hs Hvar).
    f_equal; ring.
Qed.

(** The usual form, with the combined deviation written explicitly. *)
Corollary gc_difference_sqrt :
  forall m1 s1 m2 s2 z : R,
    (0 < s1)%R -> (0 < s2)%R ->
    real_integral (fun u => gc_density m1 s1 u * gc_density m2 s2 (u - z)) =
    gc_density (m1 - m2) (sqrt (s1 * s1 + s2 * s2)) z.
Proof.
  intros m1 s1 m2 s2 z H1 H2.
  assert (HSpos : (0 < s1 * s1 + s2 * s2)%R)
    by (apply gc_sumsq_pos; assumption).
  apply gc_difference; try assumption.
  - apply sqrt_lt_R0; exact HSpos.
  - apply sqrt_sqrt; lra.
Qed.

(** * The program, and the statement about it that is NOT provable

    The density result above says the normal family is closed under
    differences.  The corresponding statement about PROGRAMS is that
    sampling twice and subtracting is interchangeable with sampling once
    from the combined normal. *)

Definition gc_x : RealProgramVar := real_program_var "gc_x".
Definition gc_y : RealProgramVar := real_program_var "gc_y".
Definition gc_d : RealProgramVar := real_program_var "gc_d".

Definition gc_minus_one : Term := TConst (-1).

Definition gc_normal (m s : R) : Distribution := <{ gaussian(m, s) }>.

Definition gc_gap : Term := <{ gc_x + $(gc_minus_one) * gc_y }>.

Definition gc_two_sample (m1 s1 m2 s2 : R) : Cmd :=
  <{ gc_x sample $(gc_normal m1 s1);
     gc_y sample $(gc_normal m2 s2);
     gc_d := $(gc_gap) }>.

Definition gc_one_sample (m s : R) : Cmd :=
  <{ gc_d sample $(gc_normal m s) }>.

(** Their weakest preconditions for the event [gc_d < t]. *)

Definition gc_two_wp (m1 s1 m2 s2 t : R) : PConstruct :=
  [[ integral gc_x ~ $(gc_normal m1 s1),
     integral gc_y ~ $(gc_normal m2 s2),
     indicator[ $(gc_gap) < t ] ]].

Definition gc_one_wp (m s t : R) : PConstruct :=
  [[ integral gc_d ~ $(gc_normal m s), indicator[ gc_d < t ] ]].

(** These really are the weakest preconditions -- definitional, so the
    statement below is about the programs, not an invented formula. *)

Lemma gc_two_wp_is_wp :
  forall m1 s1 m2 s2 t r : R,
    sample_pformula gc_x (gc_normal m1 s1)
      (sample_pformula gc_y (gc_normal m2 s2)
        (subst_real_pformula gc_d gc_gap [[ Pr[gc_d < t] = $(r) ]])) =
    [[ E[ $(gc_two_wp m1 s1 m2 s2 t) ] = $(r) ]].
Proof. intros; reflexivity. Qed.

Lemma gc_one_wp_is_wp :
  forall m s t r : R,
    sample_pformula gc_d (gc_normal m s) [[ Pr[gc_d < t] = $(r) ]] =
    [[ E[ $(gc_one_wp m s t) ] = $(r) ]].
Proof. intros; reflexivity. Qed.

(** STATED, NOT PROVED.  "Sample twice and subtract" and "sample once from
    the combined normal" have the same weakest precondition, hence satisfy
    exactly the same triples. *)
Definition gc_program_target (m1 s1 m2 s2 s t : R) : Prop :=
  forall v : state,
    q_eval (gc_two_wp m1 s1 m2 s2 t) v = q_eval (gc_one_wp (m1 - m2) s t) v.

(**
  WHY IT IS NOT PROVED.  Unfolding, [gc_program_target] asks for

      INT phi_{m1,s1}(u) [ INT phi_{m2,s2}(w) H(u - w) dw ] du
        =  INT phi_{m1-m2,s}(k) H(k) dk

  for the indicator [H] of [. < t].  This needs a translation change of
  variables in the inner integral and Fubini for the product of the two
  kernel measures; [gc_difference] above is exactly the resulting density
  identity, but the measure-theoretic reorganisation of the nested kernel
  integrals has not been carried out in this development.
*)
