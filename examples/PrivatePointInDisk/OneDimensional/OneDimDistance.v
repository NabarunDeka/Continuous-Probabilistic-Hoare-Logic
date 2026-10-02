(**
  OneDimDistance.v -- the ONE-DIMENSIONAL private membership test, with the
  noise applied to the DIFFERENCE.

      e      := p - c;
      n      <- sample(Laplace(0, b));
      e      := e + n;
      inside := (-1 <= e  /\  e < 1)

  THE TRIPLE ([od_correct], for [0 < b], writing [D] for the true difference
  [p - c]):

      { Pr[tt] = 1 }
          od_prog p c b
      { Pr[inside] = laplace_cdf 0 b (1 - D) - laplace_cdf 0 b (-1 - D) }

  WHY THIS FILE EXISTS.  In one dimension "inside the unit ball" is the
  INTERVAL [-1 <= x < 1], not a disk.  An interval has CONSTANT endpoints,
  so the reachability criterion of UniformConstructions/TriangularRejection.v
  -- sections must be intervals with polynomial endpoints -- is satisfied
  trivially, and no square root ever appears.  This is the 1-D counterpart of
  PointInDiskAdditive.v and is the easy half of the pair; the interesting
  half is OneDimPoints.v, which perturbs the two points separately.

  Together the two files isolate what actually blocks the two-dimensional
  four-noise variant: it is the DISK, not the double perturbation.  See
  flags/FLAGS.md F14.

  The window is half-open ([-1 <= e < 1]) to match CPHL.v's strict-CDF closed
  form, which is the only endpoint convention available (F6).  Under
  continuous noise the endpoints carry no mass, so this agrees with the
  closed test.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import HalfLaplaceRejection.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program

    [p] and [c] are Rocq reals, so [od_diff] is a CLOSED term -- the same
    device as in PointInDiskAdditive.v, and for the same reason. *)

Definition od_e : RealProgramVar := real_program_var "od_e".
Definition od_n : RealProgramVar := real_program_var "od_n".
Definition od_inside : BoolProgramVar := bool_program_var "od_inside".

Definition od_minus_one : Term := TConst (-1).

Definition od_diff (p c : R) : Term := <{ $(p) + $(od_minus_one) * $(c) }>.

Definition od_D (p c : R) : R := (p - c)%R.

Definition od_noise (b : R) : Distribution := <{ laplace(0, b) }>.

Definition od_shift : Term := <{ od_e + od_n }>.

Definition od_window : CFormula :=
  <{ ($(od_minus_one) <= od_e) /\ (od_e < 1) }>.

Definition od_prog (p c b : R) : Cmd :=
  <{ od_e      := $(od_diff p c);
     od_n      sample $(od_noise b);
     od_e      := $(od_shift);
     od_inside b= $(od_window) }>.

(** The answer: the Laplace mass of the window, recentred on [D]. *)
Definition od_answer (p c b : R) : R :=
  (laplace_cdf 0 b (1 - od_D p c) - laplace_cdf 0 b (-1 - od_D p c))%R.

(** * Two small analytic facts *)

Lemma od_integral_minus :
  forall f g : R -> R,
    real_integral (fun x => (f x - g x)%R) =
    (real_integral f - real_integral g)%R.
Proof.
  intros f g.
  transitivity (real_integral (fun x => (f x + (-1) * g x)%R)).
  - apply real_integral_extensional; intro x; ring.
  - rewrite real_integral_add, real_integral_scale; ring.
Qed.

(** A half-open window is the difference of two half-lines. *)
Lemma od_window_indicator :
  forall A B z : R,
    (A <= B)%R ->
    real_indicator (A <= z < B)%R =
    (real_indicator (z < B)%R - real_indicator (z < A)%R)%R.
Proof.
  intros A B z Hab.
  destruct (Rlt_dec z A) as [H1 | H1].
  - rewrite (real_indicator_false (A <= z < B)%R) by (intros [Ha _]; lra).
    rewrite (real_indicator_true (z < A)%R H1).
    rewrite (real_indicator_true (z < B)%R) by lra.
    ring.
  - destruct (Rlt_dec z B) as [H2 | H2].
    + rewrite (real_indicator_true (A <= z < B)%R
                 (conj (Rnot_lt_le _ _ H1) H2)).
      rewrite (real_indicator_false (z < A)%R) by lra.
      rewrite (real_indicator_true (z < B)%R H2).
      ring.
    + rewrite (real_indicator_false (A <= z < B)%R) by (intros [_ Hb]; lra).
      rewrite (real_indicator_false (z < A)%R) by lra.
      rewrite (real_indicator_false (z < B)%R) by lra.
      ring.
Qed.

Lemma od_diff_value :
  forall (p c : R) (v : state),
    term_eval (od_diff p c) v = od_D p c.
Proof.
  intros p c v.
  unfold od_diff, od_minus_one, od_D.
  cbn [term_eval]; ring.
Qed.

(** [c_and] is encoded through implication, so unpacking it is classical. *)
Lemma od_satisfies_c_and :
  forall (v : state) (g1 g2 : CFormula),
    satisfies v <{ $(g1) /\ $(g2) }> <-> (satisfies v g1 /\ satisfies v g2).
Proof.
  intros v g1 g2.
  cbn [c_and c_not satisfies].
  split.
  - intro H.
    destruct (classic (satisfies v g1)) as [H1 | H1];
      destruct (classic (satisfies v g2)) as [H2 | H2];
      try (split; assumption);
      exfalso; apply H; intros Ha Hb; contradiction.
  - intros [H1 H2] Hc; exact (Hc H1 H2).
Qed.

(** * The single integral produced by the sample *)

Lemma od_integral :
  forall (p c b : R) (v : state),
    (0 < b)%R ->
    q_eval
      [[ integral od_n ~ $(Laplace (TConst 0) (TConst b)),
         indicator[ ($(od_minus_one) <= $(od_diff p c) + od_n)
                    /\ ($(od_diff p c) + od_n < 1) ] ]] v
    = od_answer p c b.
Proof.
  intros p c b v Hb.
  unfold od_answer.
  cbn [q_eval distribution_density].
  rewrite (real_integral_extensional
             _ (fun z =>
                  ((1 / (2 * b)) * exp (- Rabs (z - 0) / b))
                  * real_indicator (z < 1 - od_D p c)%R
                  - ((1 / (2 * b)) * exp (- Rabs (z - 0) / b))
                    * real_indicator (z < -1 - od_D p c)%R)).
  - rewrite od_integral_minus.
    rewrite !laplace_integral_strict_cdf by exact Hb.
    reflexivity.
  - intro z.
    rewrite (real_indicator_extensional
               _ ((-1 - od_D p c <= z) /\ (z < 1 - od_D p c))%R).
    2:{ rewrite od_satisfies_c_and.
        unfold od_minus_one, c_lt, update_real, update_real_values.
        cbn [satisfies c_not term_eval real_program_values].
        rewrite !rpv_eq_dec_refl.
        rewrite od_diff_value.
        split; intros [H1 H2]; split; lra. }
    rewrite (od_window_indicator (-1 - od_D p c) (1 - od_D p c) z) by lra.
    cbn [term_eval]; ring.
Qed.

(** * The weakest precondition *)

Definition od_post (p c b : R) : PFormula :=
  [[ Pr[od_inside] = $(od_answer p c b) ]].

Definition od_after_add (p c b : R) : PFormula :=
  subst_bool_pformula od_inside od_window (od_post p c b).

Definition od_after_sample (p c b : R) : PFormula :=
  subst_real_pformula od_e od_shift (od_after_add p c b).

Definition od_after_assign (p c b : R) : PFormula :=
  sample_pformula od_n (od_noise b) (od_after_sample p c b).

Definition od_pre (p c b : R) : PFormula :=
  [[ E[ integral od_n ~ $(Laplace (TConst 0) (TConst b)),
        indicator[ ($(od_minus_one) <= $(od_diff p c) + od_n)
                   /\ ($(od_diff p c) + od_n < 1) ] ]
     = $(od_answer p c b) ]].

(** The opening assignment closes the window's GUARD; [od_n] stays bound. *)
Lemma od_pre_is_wp :
  forall p c b : R,
    subst_real_pformula od_e (od_diff p c) (od_after_assign p c b) =
    od_pre p c b.
Proof. intros; reflexivity. Qed.

Lemma od_normalized_implies_pre :
  forall p c b : R,
    (0 < b)%R ->
    pformula_valid [[ Pr[true] = 1 -> $(od_pre p c b) ]].
Proof.
  intros p c b Hb ps Hadm.
  cbn [psatisfies]; intro Hpre.
  apply psatisfies_p_eq in Hpre.
  cbn [pterm_eval] in Hpre.
  unfold od_pre.
  apply psatisfies_p_eq.
  cbn [pterm_eval].
  apply t3_expect_const.
  - exact Hpre.
  - intro v; apply od_integral; exact Hb.
Qed.

Lemma od_noise_valid_under :
  forall (b : R) (pre : PFormula),
    (0 < b)%R ->
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula (od_noise b))] ]].
Proof.
  intros b pre Hb ps Hadm.
  cbn [psatisfies]; intro Hignore.
  clear Hignore; revert ps.
  apply p_almost_sure_of_pointwise.
  intro v.
  unfold od_noise.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The mechanism *)

Theorem od_correct :
  forall p c b : R,
    (0 < b)%R ->
    {{ Pr[true] = 1 }}
      $(od_prog p c b)
    {{ Pr[od_inside] = $(od_answer p c b) }}.
Proof.
  intros p c b Hb.
  unfold od_prog.
  eapply HSeq with (eta2 := od_after_assign p c b).
  - eapply HConseq with
      (eta1 := subst_real_pformula od_e (od_diff p c) (od_after_assign p c b))
      (eta2 := od_after_assign p c b).
    + rewrite od_pre_is_wp.
      apply od_normalized_implies_pre; exact Hb.
    + apply HRealAssign.
    + intro ps; cbn [psatisfies]; tauto.
  - eapply HSeq with (eta2 := od_after_sample p c b).
    + apply HRealSample.
      * intro ps; cbn [psatisfies]; intro H; exact H.
      * apply od_noise_valid_under; exact Hb.
    + eapply HSeq with (eta2 := od_after_add p c b).
      * apply HRealAssign.
      * apply HBoolAssign.
Qed.
