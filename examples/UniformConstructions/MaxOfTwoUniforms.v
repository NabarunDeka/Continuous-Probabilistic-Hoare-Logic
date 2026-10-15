(**
  MaxOfTwoUniforms.v

  Program ([mx_prog]):
      mx_x <- sample(uniform(0, 1)); mx_y <- sample(uniform(0, 1))
  Triple ([mx_correct], for 0 <= t <= 1; event [mx_event t]):
      { E[1_tt] = mx_w }  mx_prog  { E[1_(mx_x < t /\ mx_y < t)] = t * t * mx_w }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Require Import CPHL.
Require Import CPHLFacts.CalculationFacts.
Require Import SampleBeforeLoop.
Require Import PersistentSampleLoop.
Require Import HalfLaplaceRejection CdfAssertions.
Require Import UniformAxiomsAdditional.
Require Import UniformRejectionSampling.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program *)

Definition mx_x : RealProgramVar := real_program_var "mx_x".
Definition mx_y : RealProgramVar := real_program_var "mx_y".
Definition mx_w : ProbLogicVar := prob_logic_var "mx_w".

Lemma mx_x_neq_y : mx_x <> mx_y.
Proof. unfold mx_x, mx_y; intro H; inversion H. Qed.

Definition mx_unit : Distribution := <{ uniform(0, 1) }>.

Definition mx_event (t : R) : CFormula :=
  <{ (mx_x < t) /\ (mx_y < t) }>.

Definition mx_prog : Cmd :=
  <{ mx_x sample $(mx_unit);
     mx_y sample $(mx_unit) }>.

(** * The event factors *)

Lemma mx_val_x :
  forall (v : state) (k m : R),
    real_program_values
      (update_real (update_real v mx_x k) mx_y m) mx_x = k.
Proof.
  intros v k m.
  unfold update_real, update_real_values.
  cbn [real_program_values].
  rewrite (rpv_eq_dec_neq mx_x mx_y _ _ _ mx_x_neq_y).
  rewrite rpv_eq_dec_refl.
  reflexivity.
Qed.

Lemma mx_val_y :
  forall (v : state) (k m : R),
    real_program_values
      (update_real (update_real v mx_x k) mx_y m) mx_y = m.
Proof.
  intros v k m.
  unfold update_real, update_real_values.
  cbn [real_program_values].
  rewrite rpv_eq_dec_refl.
  reflexivity.
Qed.

Lemma mx_indicator :
  forall (t : R) (v : state) (k m : R),
    real_indicator
      (satisfies (update_real (update_real v mx_x k) mx_y m) (mx_event t)) =
    (real_indicator (k < t)%R * real_indicator (m < t)%R)%R.
Proof.
  intros t v k m.
  rewrite (real_indicator_extensional _ ((k < t)%R /\ (m < t)%R)).
  - apply ur_real_indicator_and.
  - unfold mx_event, c_lt, c_not.
    rewrite satisfies_c_and.
    cbn [satisfies term_eval].
    rewrite mx_val_x, mx_val_y.
    split.
    + intro H.
      destruct H as [Hx Hy].
      split.
      * destruct (Rlt_dec k t) as [Hd | Hd]; [exact Hd |].
        exfalso; apply Hx; lra.
      * destruct (Rlt_dec m t) as [Hd | Hd]; [exact Hd |].
        exfalso; apply Hy; lra.
    + intro H.
      destruct H as [Hk Hm].
      split; intro Hc; lra.
Qed.

(** * Both integrals are constants on intervals *)

Lemma mx_inner :
  forall (t : R) (v : state) (k : R),
    (0 <= t)%R -> (t <= 1)%R ->
    q_eval (QIntegral mx_y mx_unit (QIndicator (mx_event t)))
      (update_real v mx_x k) =
    (real_indicator (k < t)%R * t)%R.
Proof.
  intros t v k H0 H1.
  unfold mx_unit; rewrite q_eval_unit_uniform.
  destruct (Rlt_dec k t) as [Hk | Hk].
  - rewrite (real_indicator_true _ Hk).
    rewrite (real_integral_extensional _
               (fun m => real_indicator (0 <= m < t)%R * 1)).
    + rewrite real_integral_open_const by lra; ring.
    + intro m; rewrite q_eval_indicatorE, mx_indicator,
        (real_indicator_true (k < t)%R Hk).
      destruct (Rlt_dec m t) as [Hm | Hm].
      * rewrite (real_indicator_true (m < t)%R Hm).
        destruct (Rle_dec 0 m) as [Hm0 | Hm0].
        -- rewrite (real_indicator_true (0 <= m <= 1)%R) by lra.
           rewrite (real_indicator_true (0 <= m < t)%R) by lra; ring.
        -- rewrite (real_indicator_false (0 <= m <= 1)%R) by lra.
           rewrite (real_indicator_false (0 <= m < t)%R) by lra; ring.
      * rewrite (real_indicator_false (m < t)%R Hm).
        rewrite (real_indicator_false (0 <= m < t)%R) by lra; ring.
  - rewrite (real_indicator_false _ Hk).
    rewrite (real_integral_extensional _ (fun _ => 0%R)).
    + rewrite real_integral_zero; ring.
    + intro m; rewrite q_eval_indicatorE, mx_indicator,
        (real_indicator_false (k < t)%R Hk); ring.
Qed.

Lemma mx_qeval :
  forall (t : R) (v : state),
    (0 <= t)%R -> (t <= 1)%R ->
    q_eval
      (QIntegral mx_x mx_unit (QIntegral mx_y mx_unit (QIndicator (mx_event t))))
      v = (t * t)%R.
Proof.
  intros t v H0 H1.
  unfold mx_unit at 1; rewrite q_eval_unit_uniform.
  rewrite (real_integral_extensional _
             (fun k => real_indicator (0 <= k < t)%R * t)).
  - rewrite real_integral_open_const by lra; ring.
  - intro k; rewrite (mx_inner t v k H0 H1).
    destruct (Rlt_dec k t) as [Hk | Hk].
    + rewrite (real_indicator_true (k < t)%R Hk).
      destruct (Rle_dec 0 k) as [Hk0 | Hk0].
      * rewrite (real_indicator_true (0 <= k <= 1)%R) by lra.
        rewrite (real_indicator_true (0 <= k < t)%R) by lra; ring.
      * rewrite (real_indicator_false (0 <= k <= 1)%R) by lra.
        rewrite (real_indicator_false (0 <= k < t)%R) by lra; ring.
    + rewrite (real_indicator_false (k < t)%R Hk).
      rewrite (real_indicator_false (0 <= k < t)%R) by lra; ring.
Qed.

(** * The theorem

    No loop, hence no [while_progress], hence [t = 0] is fine. *)

Lemma mx_unit_valid_under :
  forall pre : PFormula,
    pformula_valid
      (PFImpl pre (p_almost_sure (distribution_valid_formula mx_unit))).
Proof.
  intros pre ps Hadm _.
  refine (p_almost_sure_of_pointwise _ _ ps Hadm).
  intro v.
  unfold mx_unit.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

Theorem mx_correct :
  forall t : R,
    (0 <= t)%R -> (t <= 1)%R ->
    {{ Pr[true] = mx_w }}
      $(mx_prog)
    {{ Pr[$(mx_event t)] = $(t * t) * mx_w }}.
Proof.
  intros t H0 H1.
  unfold mx_prog.
  eapply HSeq with
    (eta2 :=
       sample_pformula mx_y mx_unit
         (p_eq (PExpect (QIndicator (mx_event t)))
            (PMul (PConst (t * t)) (PVar mx_w)))).
  - apply HRealSample; [| apply mx_unit_valid_under].
    intros ps Hadm.
    cbn [psatisfies].
    intro Hpre.
    apply psatisfies_p_eq in Hpre.
    cbn [pterm_eval] in Hpre.
    rewrite !sample_pformula_p_eq.
    apply psatisfies_p_eq.
    cbn [sample_pterm pterm_eval].
    rewrite (expect_const_construct _ _ (t * t)%R), Hpre;
      [reflexivity | intro v; apply mx_qeval; assumption].
  - apply HRealSample; [| apply mx_unit_valid_under].
    intros ps Hadm; cbn [psatisfies]; intro H; exact H.
Qed.
