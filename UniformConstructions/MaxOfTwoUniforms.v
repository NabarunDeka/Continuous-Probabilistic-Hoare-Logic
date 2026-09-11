(**
  MaxOfTwoUniforms.v -- the same law as TriangularRejection.v, by a route
  that needs NO moment axiom.  A cross-check on the axiom that file adds.

      x <- sample(Uniform(0,1));
      y <- sample(Uniform(0,1))

  THE TRIPLE ([mx_correct], for [0 <= t <= 1]):

      { E[1_tt] = w }
          mx_prog
      { Pr[x < t  /\  y < t]  =  t * t * w }

  [x < t /\ y < t] is [max(x,y) < t], so this is the CDF of the maximum of
  two independent uniforms -- the same Beta(2,1) law that
  TriangularRejection.v obtains by rejection.

  WHY IT IS HERE.  The two routes are analytically independent:

    - TriangularRejection.v accepts iff [y < x].  That does NOT factor, the
      inner integral returns a function of the outer variable, and the outer
      integral needs [real_integral_between_linear].
    - Here the event DOES factor into an x-part and a y-part, so the inner
      integral collapses to the constant [uniform_cdf 0 1 t] and the outer
      is another CDF.  The answer [t * t] is a product of two CDFs and needs
      no moment law at all.

  So if [real_integral_between_linear] were wrong, these two files would
  disagree.  [Print Assumptions mx_correct] should NOT mention it.

  ONE MORE DIFFERENCE.  This file has no loop, so no [while_progress], so
  [t = 0] is allowed -- and gives probability 0, correctly.
  TriangularRejection.v cannot reach [t = 0] at all.  The boundary gap there
  is a property of the WHILE RULE, not of the mathematics, and this file is
  the evidence.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import PersistentSampleLoop.
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

Lemma mx_density_eq :
  forall (v : state) (z : R),
    distribution_density mx_unit v z = uniform_density_R 0 1 z.
Proof. reflexivity. Qed.

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

(** * Both integrals are plain CDFs *)

Lemma mx_inner :
  forall (t : R) (v : state) (k : R),
    q_eval (QIntegral mx_y mx_unit (QIndicator (mx_event t)))
      (update_real v mx_x k) =
    (real_indicator (k < t)%R * uniform_cdf 0 1 t)%R.
Proof.
  intros t v k.
  rewrite q_eval_integral.
  transitivity
    (real_indicator (k < t)%R *
     real_integral
       (fun m => uniform_density_R 0 1 m * real_indicator (m < t)%R))%R.
  - rewrite <- real_integral_scale.
    apply real_integral_extensional; intro m.
    rewrite mx_density_eq.
    cbn [q_eval].
    rewrite mx_indicator.
    ring.
  - rewrite uniform_integral_strict_cdf by lra.
    reflexivity.
Qed.

Lemma mx_qeval :
  forall (t : R) (v : state),
    (0 <= t)%R -> (t <= 1)%R ->
    q_eval
      (QIntegral mx_x mx_unit (QIntegral mx_y mx_unit (QIndicator (mx_event t))))
      v = (t * t)%R.
Proof.
  intros t v H0 H1.
  rewrite q_eval_integral.
  transitivity
    (uniform_cdf 0 1 t *
     real_integral
       (fun k => uniform_density_R 0 1 k * real_indicator (k < t)%R))%R.
  - rewrite <- real_integral_scale.
    apply real_integral_extensional; intro k.
    rewrite mx_density_eq, (mx_inner t).
    ring.
  - rewrite uniform_integral_strict_cdf by lra.
    rewrite (uniform_cdf_unit t) by assumption.
    reflexivity.
Qed.

(** * The theorem

    No loop, hence no [while_progress], hence [t = 0] is fine. *)

Lemma mx_unit_valid_under :
  forall pre : PFormula,
    pformula_valid
      (PFImpl pre (p_almost_sure (distribution_valid_formula mx_unit))).
Proof.
  intros pre ps.
  cbn [psatisfies]; intro Hignore.
  clear Hignore; revert ps.
  apply p_almost_sure_of_pointwise.
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
    intro ps.
    cbn [psatisfies].
    intro Hpre.
    apply psatisfies_p_eq in Hpre.
    cbn [pterm_eval] in Hpre.
    rewrite !sample_pformula_p_eq.
    apply psatisfies_p_eq.
    cbn [sample_pterm pterm_eval].
    transitivity
      (expectation (pstate_measure ps) (fun _ : state => (t * t)%R)).
    + apply expectation_extensional; intro v.
      apply mx_qeval; assumption.
    + rewrite expectation_constant, Hpre; reflexivity.
  - apply HRealSample; [| apply mx_unit_valid_under].
    intro ps; cbn [psatisfies]; intro H; exact H.
Qed.
