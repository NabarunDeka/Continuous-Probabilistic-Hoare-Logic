(**
  UniformAxiomsAdditional.v -- the analytic laws CPHL.v is missing for the
  uniform distribution.

  NO TRIPLE.  This is the only file under examples/ that proves no Hoare
  triple: it contains no command, no assertion and no program variable, only
  axioms and lemmas about [real_integral].  It is the support module for
  UniformRejectionSampling.v, TriangularRejection.v and MaxOfTwoUniforms.v,
  which do state triples.

  [CPHL.v] gives closed forms for exponential region integrals, which is
  enough for every Laplace calculation.  It gives NOTHING for [Uniform]:
  the constructor, its density and its validity condition exist, but no
  lemma evaluates a uniform integral.  This file supplies the two missing
  laws and derives the usual CDF machinery from them.

  TWO AXIOMS, AND WHY THE SECOND IS NEEDED.

  After pulling out the constant [1/(u-l)], every uniform integrand is the
  indicator of a bounded interval, so ONE law -- the length of an interval
  -- carries almost all the weight.

  The second is an artefact of a mismatch inside [CPHL.v].  Its region
  operators use HALF-OPEN intervals, and a comment says this was chosen to
  "avoid requiring a separate zero-mass-at-an-endpoint axiom".  But the
  uniform density is written over a CLOSED interval,

      real_indicator (l <= z /\ z <= u) / (u - l),

  so the endpoint axiom that design avoided becomes unavoidable the moment
  the density is integrated.  It bites in exactly two places: total mass,
  and the CDF above the top of the support.  Everywhere strictly inside,
  [l, t) is already half-open and the first law alone suffices.

  The cleaner alternative is to change the density to [l <= z < u], after
  which [real_integral_point_null] is not needed at all.  That is a change
  to CPHL.v rather than an addition, so it is not taken here.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
Require Import CPHL.

Open Scope R_scope.

(** * The two added laws *)

(** Stated in CPHL's own region vocabulary, mirroring
    [real_integral_exp_between]. *)
Axiom real_integral_between_length :
  forall a b : R,
    (a <= b)%R ->
    real_integral_between a b (fun _ => 1%R) = (b - a)%R.

(** A function supported on a single point integrates to zero.  The [f] is
    carried because the endpoint appears multiplied by other indicators. *)
Axiom real_integral_point_null :
  forall (c : R) (f : R -> R),
    real_integral (fun z => real_indicator (z = c)%R * f z) = 0%R.

(** The form actually used below. *)
Lemma real_integral_indicator_interval :
  forall a b : R,
    (a <= b)%R ->
    real_integral (fun z => real_indicator (a <= z < b)%R) = (b - a)%R.
Proof.
  intros a b Hab.
  rewrite <- (real_integral_between_length a b Hab).
  unfold real_integral_between.
  apply real_integral_extensional; intro z; ring.
Qed.

(** * The uniform density and CDF *)

Definition uniform_density_R (l u z : R) : R :=
  (real_indicator (l <= z <= u)%R / (u - l))%R.

Definition uniform_cdf (l u t : R) : R :=
  if Rle_dec t l then 0%R
  else if Rle_dec u t then 1%R
  else ((t - l) / (u - l))%R.

(** Splitting a closed interval into its half-open part and its endpoint --
    the only place the second axiom is needed. *)
Lemma real_indicator_closed_split :
  forall l u z : R,
    (l <= u)%R ->
    real_indicator (l <= z <= u)%R =
    (real_indicator (l <= z < u)%R + real_indicator (z = u)%R)%R.
Proof.
  intros l u z Hlu.
  destruct (Rlt_dec z l) as [Hzl | Hzl].
  - rewrite (real_indicator_false (l <= z <= u)%R) by (intros [H1 H2]; lra).
    rewrite (real_indicator_false (l <= z < u)%R) by (intros [H1 H2]; lra).
    rewrite (real_indicator_false (z = u)%R) by lra.
    ring.
  - destruct (Rlt_dec z u) as [Hzu | Hzu].
    + rewrite (real_indicator_true (l <= z <= u)%R) by lra.
      rewrite (real_indicator_true (l <= z < u)%R) by lra.
      rewrite (real_indicator_false (z = u)%R) by lra.
      ring.
    + destruct (Req_dec z u) as [Hzeq | Hzeq].
      * rewrite (real_indicator_true (l <= z <= u)%R) by lra.
        rewrite (real_indicator_false (l <= z < u)%R) by (intros [H1 H2]; lra).
        rewrite (real_indicator_true (z = u)%R Hzeq).
        ring.
      * rewrite (real_indicator_false (l <= z <= u)%R) by (intros [H1 H2]; lra).
        rewrite (real_indicator_false (l <= z < u)%R) by (intros [H1 H2]; lra).
        rewrite (real_indicator_false (z = u)%R) by lra.
        ring.
Qed.

(** * The CDF, in closed form *)

Lemma uniform_integral_strict_cdf :
  forall l u t : R,
    (l < u)%R ->
    real_integral
      (fun z => uniform_density_R l u z * real_indicator (z < t)%R) =
    uniform_cdf l u t.
Proof.
  intros l u t Hlu.
  unfold uniform_cdf.
  destruct (Rle_dec t l) as [Htl | Htl].
  - (* below the support: the integrand vanishes *)
    rewrite (real_integral_extensional _ (fun _ => 0%R)).
    + apply real_integral_zero.
    + intro z.
      unfold uniform_density_R.
      destruct (Rlt_dec z t) as [Hzt | Hzt].
      * rewrite (real_indicator_false (l <= z <= u)%R)
          by (intros [H1 H2]; lra).
        unfold Rdiv; ring.
      * rewrite (real_indicator_false (z < t)%R) by lra; ring.
  - destruct (Rle_dec u t) as [Hut | Hut].
    + (* above the support: all the mass *)
      rewrite (real_integral_extensional _
                 (fun z =>
                    (real_indicator (l <= z < u)%R +
                     real_indicator (z = u)%R * real_indicator (z < t)%R) *
                    / (u - l))).
      * rewrite real_integral_scale_right, real_integral_add.
        rewrite (real_integral_indicator_interval l u) by lra.
        rewrite (real_integral_point_null u (fun z => real_indicator (z < t)%R)).
        field; lra.
      * intro z.
        unfold uniform_density_R, Rdiv.
        rewrite (real_indicator_closed_split l u z) by lra.
        destruct (Rlt_dec z u) as [Hzu | Hzu].
        -- rewrite (real_indicator_true (z < t)%R) by lra.
           rewrite (real_indicator_false (z = u)%R) by lra.
           ring.
        -- rewrite (real_indicator_false (l <= z < u)%R)
             by (intros [H1 H2]; lra).
           ring.
    + (* strictly inside: a proper fraction *)
      rewrite (real_integral_extensional _
                 (fun z => real_indicator (l <= z < t)%R * / (u - l))).
      * rewrite real_integral_scale_right.
        rewrite (real_integral_indicator_interval l t) by lra.
        field; lra.
      * intro z.
        unfold uniform_density_R, Rdiv.
        destruct (Rlt_dec z t) as [Hzt | Hzt].
        -- rewrite (real_indicator_true (z < t)%R Hzt).
           destruct (Rle_dec l z) as [Hlz | Hlz].
           ++ rewrite (real_indicator_true (l <= z <= u)%R) by lra.
              rewrite (real_indicator_true (l <= z < t)%R) by lra.
              ring.
           ++ rewrite (real_indicator_false (l <= z <= u)%R)
                by (intros [H1 H2]; lra).
              rewrite (real_indicator_false (l <= z < t)%R)
                by (intros [H1 H2]; lra).
              ring.
        -- rewrite (real_indicator_false (z < t)%R) by lra.
           rewrite (real_indicator_false (l <= z < t)%R)
             by (intros [H1 H2]; lra).
           ring.
Qed.

(** Total mass is the CDF above the support. *)
Lemma uniform_density_total :
  forall l u : R,
    (l < u)%R ->
    real_integral (uniform_density_R l u) = 1%R.
Proof.
  intros l u Hlu.
  transitivity
    (real_integral
       (fun z => uniform_density_R l u z * real_indicator (z < u + 1)%R)).
  - apply real_integral_extensional; intro z.
    unfold uniform_density_R.
    destruct (Rlt_dec z (u + 1)) as [Hz | Hz].
    + rewrite (real_indicator_true (z < u + 1)%R Hz); ring.
    + rewrite (real_indicator_false (z < u + 1)%R) by lra.
      rewrite (real_indicator_false (l <= z <= u)%R)
        by (intros [H1 H2]; lra).
      unfold Rdiv; ring.
  - rewrite uniform_integral_strict_cdf by exact Hlu.
    unfold uniform_cdf.
    destruct (Rle_dec (u + 1) l) as [H | H]; [lra |].
    destruct (Rle_dec u (u + 1)) as [H' | H']; [reflexivity | lra].
Qed.

(** The survival function, derived rather than assumed. *)
Lemma uniform_integral_survival :
  forall l u t : R,
    (l < u)%R ->
    real_integral
      (fun z => uniform_density_R l u z * real_indicator (t <= z)%R) =
    (1 - uniform_cdf l u t)%R.
Proof.
  intros l u t Hlu.
  assert (Hsplit :
    real_integral (uniform_density_R l u) =
    (real_integral
       (fun z => uniform_density_R l u z * real_indicator (z < t)%R) +
     real_integral
       (fun z => uniform_density_R l u z * real_indicator (t <= z)%R))%R).
  { rewrite <- real_integral_add.
    apply real_integral_extensional; intro z.
    destruct (Rlt_dec z t) as [Hz | Hz].
    - rewrite (real_indicator_true (z < t)%R Hz).
      rewrite (real_indicator_false (t <= z)%R) by lra.
      ring.
    - rewrite (real_indicator_false (z < t)%R) by lra.
      rewrite (real_indicator_true (t <= z)%R) by lra.
      ring. }
  rewrite uniform_density_total in Hsplit by exact Hlu.
  rewrite uniform_integral_strict_cdf in Hsplit by exact Hlu.
  lra.
Qed.

(** * Bounds, for the certificate's range obligations *)

Lemma uniform_cdf_bounds :
  forall l u t : R,
    (l < u)%R -> (0 <= uniform_cdf l u t <= 1)%R.
Proof.
  intros l u t Hlu.
  unfold uniform_cdf.
  destruct (Rle_dec t l) as [H | H]; [lra |].
  destruct (Rle_dec u t) as [H' | H']; [lra |].
  assert (Hval : ((t - l) / (u - l) * (u - l))%R = (t - l)%R)
    by (field; lra).
  split.
  - apply Rmult_le_reg_r with (r := (u - l)%R); [lra |].
    rewrite Hval; lra.
  - apply Rmult_le_reg_r with (r := (u - l)%R); [lra |].
    rewrite Hval; lra.
Qed.

(** * The first moment

    Rejection under a NON-constant polynomial envelope makes the inner
    integral return a function of the outer variable rather than a
    constant, so the outer integral is no longer an integral of an
    indicator.  This is the 1st-moment companion to
    [real_integral_between_length], which is the 0th.

    The general family is [int_a^b x^n = (b^(n+1) - a^(n+1))/(n+1)]; they
    are added one at a time rather than fighting [pow] and induction for no
    present gain. *)

Axiom real_integral_between_linear :
  forall a b : R,
    (a <= b)%R ->
    real_integral_between a b (fun x => x) = ((b * b - a * a) / 2)%R.

Lemma real_integral_indicator_linear :
  forall a b : R,
    (a <= b)%R ->
    real_integral (fun z => real_indicator (a <= z < b)%R * z) =
    ((b * b - a * a) / 2)%R.
Proof.
  intros a b Hab.
  rewrite <- (real_integral_between_linear a b Hab).
  unfold real_integral_between.
  apply real_integral_extensional; intro z; ring.
Qed.

Lemma real_integral_minus :
  forall f g : R -> R,
    real_integral (fun x => (f x - g x)%R) =
    (real_integral f - real_integral g)%R.
Proof.
  intros f g.
  transitivity (real_integral (fun x => (f x + (-1) * g x)%R)).
  - apply real_integral_extensional; intro x; ring.
  - rewrite real_integral_add, real_integral_scale; ring.
Qed.

(** The unit-interval CDF is the identity on its support.  Stated here
    rather than in a client file so that examples which must NOT depend on
    [real_integral_between_linear] can still use it. *)
Lemma uniform_cdf_unit :
  forall t : R, (0 <= t)%R -> (t <= 1)%R -> uniform_cdf 0 1 t = t.
Proof.
  intros t H0 H1.
  unfold uniform_cdf.
  destruct (Rle_dec t 0) as [H | H].
  - assert (Ht : t = 0%R) by lra; subst t; reflexivity.
  - destruct (Rle_dec 1 t) as [H' | H'].
    + assert (Ht : t = 1%R) by lra; subst t; reflexivity.
    + field.
Qed.
