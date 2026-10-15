(**
  TriangularRejection.v

  Program ([ta_prog]):
      ta_retry := tt;
      while ta_retry do
        ta_x <- sample(uniform(0, 1));
        ta_y <- sample(uniform(0, 1));
        ta_retry := (ta_x <= ta_y)
      end
  Triple ([ta_correct], for 0 < t <= 1; q = [ta_q t]):
      { E[1_tt] = ta_w }  ta_prog  { E[1_(ta_x < t /\ ~ta_retry)] = t * t * ta_w }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Require Import CPHL.
Require Import CPHLFacts.CalculationFacts.
Require Import SampleBeforeLoop.
Require Import PersistentSampleLoop.
Require Import HalfLaplaceRejection.
Require Import UniformAxiomsAdditional.
Require Import UniformRejectionSampling.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * The program *)

Definition ta_x : RealProgramVar := real_program_var "ta_x".
Definition ta_y : RealProgramVar := real_program_var "ta_y".
Definition ta_retry : BoolProgramVar := bool_program_var "ta_retry".
Definition ta_w : ProbLogicVar := prob_logic_var "ta_w".

Lemma ta_x_neq_y : ta_x <> ta_y.
Proof. unfold ta_x, ta_y; intro H; inversion H. Qed.

Definition ta_unit : Distribution := <{ uniform(0, 1) }>.

(** Retry exactly when the draw is rejected, i.e. when [x <= y]. *)
Definition ta_reject : CFormula := <{ ta_x <= ta_y }>.

Definition ta_below (t : R) : CFormula := <{ ta_x < t }>.

Definition ta_guard : CFormula := <{ ta_retry }>.

Definition ta_body : Cmd :=
  <{ ta_x     sample $(ta_unit);
     ta_y     sample $(ta_unit);
     ta_retry b= $(ta_reject) }>.

Definition ta_loop : Cmd := <{ while $(ta_guard) do $(ta_body) end }>.

Definition ta_prog : Cmd := <{ ta_retry b= true; $(ta_loop) }>.

(** * Reading the coordinates back after both updates *)

Lemma ta_val_x :
  forall (v : state) (k m : R),
    real_program_values
      (update_real (update_real v ta_x k) ta_y m) ta_x = k.
Proof.
  intros v k m.
  unfold update_real, update_real_values.
  cbn [real_program_values].
  rewrite (rpv_eq_dec_neq ta_x ta_y _ _ _ ta_x_neq_y).
  rewrite rpv_eq_dec_refl.
  reflexivity.
Qed.

Lemma ta_val_y :
  forall (v : state) (k m : R),
    real_program_values
      (update_real (update_real v ta_x k) ta_y m) ta_y = m.
Proof.
  intros v k m.
  unfold update_real, update_real_values.
  cbn [real_program_values].
  rewrite rpv_eq_dec_refl.
  reflexivity.
Qed.

(** The rejection test couples the two draws: this is the indicator that
    does NOT factor. *)
Lemma ta_indicator_reject :
  forall (v : state) (k m : R),
    real_indicator
      (satisfies (update_real (update_real v ta_x k) ta_y m) ta_reject) =
    real_indicator (k <= m)%R.
Proof.
  intros v k m.
  apply real_indicator_extensional.
  unfold ta_reject.
  cbn [satisfies term_eval].
  rewrite ta_val_x, ta_val_y.
  split; intro H; exact H.
Qed.

Lemma ta_indicator_accept :
  forall (t : R) (v : state) (k m : R),
    real_indicator
      (satisfies (update_real (update_real v ta_x k) ta_y m)
         <{ $(ta_below t) /\ (~ $(ta_reject)) }>) =
    (real_indicator (k < t)%R * real_indicator (m < k)%R)%R.
Proof.
  intros t v k m.
  rewrite (real_indicator_extensional _ ((k < t)%R /\ (m < k)%R)).
  - apply ur_real_indicator_and.
  - rewrite satisfies_c_and.
    unfold ta_below, ta_reject, c_lt, c_not.
    cbn [satisfies term_eval].
    rewrite ta_val_x, ta_val_y.
    split.
    + intro H.
      destruct H as [Hlt Hnr].
      split.
      * destruct (Rlt_dec k t) as [Hd | Hd]; [exact Hd |].
        exfalso; apply Hlt; lra.
      * destruct (Rlt_dec m k) as [Hd | Hd]; [exact Hd |].
        exfalso; apply Hnr; lra.
    + intro H.
      destruct H as [Hkt Hmk].
      split; intro Hc; lra.
Qed.

(** * The inner integral returns a FUNCTION of the outer variable *)

Lemma ta_inner_reject :
  forall (v : state) (k : R),
    (0 <= k <= 1)%R ->
    q_eval [[ integral ta_y ~ $(ta_unit), indicator[$(ta_reject)] ]]
      (update_real v ta_x k) = (1 - k)%R.
Proof.
  intros v k Hk.
  unfold ta_unit; rewrite q_eval_unit_uniform.
  rewrite (real_integral_extensional _
             (fun m => real_indicator (k <= m <= 1)%R * 1)).
  - rewrite real_integral_closed_const by lra; ring.
  - intro m; rewrite q_eval_indicatorE, ta_indicator_reject.
    destruct (Rle_dec k m) as [Hm | Hm].
    + rewrite (real_indicator_true (k <= m)%R Hm).
      destruct (Rle_dec m 1) as [Hm1 | Hm1].
      * rewrite (real_indicator_true (0 <= m <= 1)%R) by lra.
        rewrite (real_indicator_true (k <= m <= 1)%R) by lra; ring.
      * rewrite (real_indicator_false (0 <= m <= 1)%R) by lra.
        rewrite (real_indicator_false (k <= m <= 1)%R) by lra; ring.
    + rewrite (real_indicator_false (k <= m)%R Hm).
      rewrite (real_indicator_false (k <= m <= 1)%R) by lra; ring.
Qed.

Lemma ta_inner_accept :
  forall (t : R) (v : state) (k : R),
    (0 <= k <= 1)%R ->
    q_eval
      [[ integral ta_y ~ $(ta_unit),
         indicator[$(ta_below t) /\ (~ $(ta_reject))] ]]
      (update_real v ta_x k) =
    (real_indicator (k < t)%R * k)%R.
Proof.
  intros t v k Hk.
  unfold ta_unit; rewrite q_eval_unit_uniform.
  destruct (Rlt_dec k t) as [Hkt | Hkt].
  - rewrite (real_indicator_true _ Hkt).
    rewrite (real_integral_extensional _
               (fun m => real_indicator (0 <= m < k)%R * 1)).
    + rewrite real_integral_open_const by lra; ring.
    + intro m; rewrite q_eval_indicatorE, ta_indicator_accept,
        (real_indicator_true (k < t)%R Hkt).
      destruct (Rlt_dec m k) as [Hm | Hm].
      * rewrite (real_indicator_true (m < k)%R Hm).
        destruct (Rle_dec 0 m) as [Hm0 | Hm0].
        -- rewrite (real_indicator_true (0 <= m <= 1)%R) by lra.
           rewrite (real_indicator_true (0 <= m < k)%R) by lra; ring.
        -- rewrite (real_indicator_false (0 <= m <= 1)%R) by lra.
           rewrite (real_indicator_false (0 <= m < k)%R) by lra; ring.
      * rewrite (real_indicator_false (m < k)%R Hm).
        rewrite (real_indicator_false (0 <= m < k)%R) by lra; ring.
  - rewrite (real_indicator_false _ Hkt).
    rewrite (real_integral_extensional _ (fun _ => 0%R)).
    + rewrite real_integral_zero; ring.
    + intro m; rewrite q_eval_indicatorE, ta_indicator_accept,
        (real_indicator_false (k < t)%R Hkt); ring.
Qed.

(** * The outer integral is a genuine polynomial integral *)

Lemma ta_qeval_reject :
  forall v : state,
    q_eval
      [[ integral ta_x ~ $(ta_unit),
         integral ta_y ~ $(ta_unit),
         indicator[$(ta_reject)] ]]
      v = (1 / 2)%R.
Proof.
  intro v.
  unfold ta_unit at 1; rewrite q_eval_unit_uniform.
  rewrite (real_integral_extensional _
             (fun k => real_indicator (0 <= k < 1)%R * (1 + (-1) * k))).
  - rewrite real_integral_open_affine by lra; field.
  - intro k.
    destruct (Rle_dec 0 k) as [H0 | H0].
    + destruct (Rlt_dec k 1) as [H1 | H1].
      * rewrite (real_indicator_true (0 <= k <= 1)%R) by lra.
        rewrite (real_indicator_true (0 <= k < 1)%R) by lra.
        fold ta_unit; rewrite ta_inner_reject by lra; ring.
      * rewrite (real_indicator_false (0 <= k < 1)%R) by lra.
        destruct (Rle_dec k 1) as [H2 | H2].
        -- assert (Hk : k = 1%R) by lra; subst k.
           rewrite (real_indicator_true (0 <= 1 <= 1)%R) by lra.
           fold ta_unit; rewrite ta_inner_reject by lra; ring.
        -- rewrite (real_indicator_false (0 <= k <= 1)%R) by lra; ring.
    + rewrite (real_indicator_false (0 <= k <= 1)%R) by lra.
      rewrite (real_indicator_false (0 <= k < 1)%R) by lra; ring.
Qed.

Lemma ta_qeval_accept :
  forall (t : R) (v : state),
    (0 <= t)%R -> (t <= 1)%R ->
    q_eval
      [[ integral ta_x ~ $(ta_unit),
         integral ta_y ~ $(ta_unit),
         indicator[$(ta_below t) /\ (~ $(ta_reject))] ]] v =
    (t * t / 2)%R.
Proof.
  intros t v H0 H1.
  unfold ta_unit at 1; rewrite q_eval_unit_uniform.
  rewrite (real_integral_extensional _
             (fun k => real_indicator (0 <= k < t)%R * k)).
  - rewrite real_integral_indicator_linear by lra; field.
  - intro k.
    destruct (Rle_dec 0 k) as [Hk0 | Hk0].
    + destruct (Rle_dec k 1) as [Hk1 | Hk1].
      * rewrite (real_indicator_true (0 <= k <= 1)%R) by lra.
        fold ta_unit; rewrite (ta_inner_accept t) by lra.
        destruct (Rlt_dec k t) as [Hkt | Hkt].
        -- rewrite (real_indicator_true (k < t)%R Hkt).
           rewrite (real_indicator_true (0 <= k < t)%R) by lra; ring.
        -- rewrite (real_indicator_false (k < t)%R Hkt).
           rewrite (real_indicator_false (0 <= k < t)%R) by lra; ring.
      * rewrite (real_indicator_false (0 <= k <= 1)%R) by lra.
        rewrite (real_indicator_false (0 <= k < t)%R) by lra; ring.
    + rewrite (real_indicator_false (0 <= k <= 1)%R) by lra.
      rewrite (real_indicator_false (0 <= k < t)%R) by lra; ring.
Qed.

(** * Certificate data

    One region.  Half the pairs are rejected; of the accepted half, the
    fraction landing below [t] is [t*t]. *)

Definition ta_regions (_ : nat) : CFormula := ta_guard.
Definition ta_transitions (_ _ : nat) : R := 1 / 2.
Definition ta_exits (t : R) (_ : nat) : R := (t * t / 2)%R.
Definition ta_solution (t : R) (_ : nat) : R := (t * t)%R.
Definition ta_q (t : R) : PConstruct := [[ indicator[$(ta_below t)] ]].

Lemma ta_unit_valid_under :
  forall pre : PFormula,
    pformula_valid
      [[ $(pre) -> almost_sure[$(distribution_valid_formula ta_unit)] ]].
Proof.
  intros pre ps Hadm _.
  refine (p_almost_sure_of_pointwise _ _ ps Hadm).
  intro v.
  unfold ta_unit.
  cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
  intro Hle; lra.
Qed.

(** * The body premise *)

Lemma ta_body_step :
  forall (t : R) (i : nat),
    (0 <= t)%R -> (t <= 1)%R -> (i < 1)%nat ->
    {{ $(p_concentrated_mass (ta_regions i) (PConst 1)) }}
      $(ta_body)
    {{ $(while_body_post 1 ta_regions (ta_transitions i) ta_guard (ta_q t)
           (ta_exits t i)) }}.
Proof.
  intros t i H0 H1 Hi.
  unfold ta_body.
  eapply HSeq with
    (eta2 :=
       sample_pformula ta_y ta_unit
         (subst_bool_pformula ta_retry ta_reject
            (while_body_post 1 ta_regions (ta_transitions i) ta_guard
               (ta_q t) (ta_exits t i)))).
  - apply HRealSample; [| apply ta_unit_valid_under].
    intros ps Hadm.
    cbn [psatisfies].
    intro Hpre.
    apply psatisfies_p_and in Hpre.
    destruct Hpre as [_ Hmass].
    apply psatisfies_p_eq in Hmass.
    cbn [pterm_eval] in Hmass.
    unfold while_body_post, ta_q, ta_regions, ta_guard, ta_transitions,
      ta_exits.
    cbn [finite_p_and condition_pconstruct condition_pconstruct_fuel
         pconstruct_size].
    rewrite !subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
    rewrite !sample_pformula_p_and, !sample_pformula_p_eq.
    apply psatisfies_p_and; split; [apply psatisfies_p_and; split | ].
    + apply psatisfies_p_true.
    + apply psatisfies_p_eq.
      cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
           pconstruct_size subst_bool_cformula
           sample_pterm pterm_eval].
      rewrite !bpv_eq_dec_refl.
      rewrite (t3_expect_const ps _ (1 / 2)%R Hmass);
        [reflexivity | intro v; apply ta_qeval_reject].
    + apply psatisfies_p_eq.
      cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
           pconstruct_size subst_bool_cformula
           ta_below c_and c_not c_lt sample_pterm pterm_eval].
      rewrite !bpv_eq_dec_refl.
      rewrite (t3_expect_const ps _ (t * t / 2)%R Hmass);
        [reflexivity | intro v; apply ta_qeval_accept; assumption].
  - eapply HSeq with
      (eta2 :=
         subst_bool_pformula ta_retry ta_reject
           (while_body_post 1 ta_regions (ta_transitions i) ta_guard
              (ta_q t) (ta_exits t i))).
    + apply HRealSample; [| apply ta_unit_valid_under].
      intros ps Hadm; cbn [psatisfies]; intro H; exact H.
    + apply HBoolAssign.
Qed.

(** * The loop

    [0 < t] strictly: [while_progress] needs the target exit mass
    [t*t/2] to be positive, and it vanishes at [t = 0]. *)

Lemma ta_loop_derivable :
  forall t : R,
    (0 < t)%R -> (t <= 1)%R ->
    {{ $(p_concentrated_mass (ta_regions 0) (PVar ta_w)) }}
      $(ta_loop)
    {{ E[$(condition_pconstruct (ta_q t) (c_not ta_guard))]
         = $(ta_solution t 0) * ta_w }}.
Proof.
  intros t H0 H1.
  assert (Hsq0 : (0 < t * t)%R) by nra.
  assert (Hsq1 : (t * t <= 1)%R) by nra.
  eapply HWhile with
    (m := 1%nat) (k := 0%nat)
    (regions := ta_regions) (solution := ta_solution t)
    (exits := ta_exits t) (transitions := ta_transitions).
  - lia.
  - unfold while_regions_cover, cformula_valid, ta_regions.
    intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
  - unfold while_regions_in_guard, cformula_valid, ta_regions.
    intros i Hi v; cbn [satisfies]; tauto.
  - unfold while_regions_disjoint; intros i j Hi Hj; lia.
  - unfold while_progress, ta_exits.
    intros i Hi; left; lra.
  - intros i Hi; apply ta_body_step; [lra | lra | exact Hi].
  - unfold while_solution, ta_solution, ta_transitions, ta_exits.
    intros i Hi; cbn [finite_r_sum]; split; lra.
Qed.

(** * The sampler *)

Theorem ta_correct :
  forall t : R,
    (0 < t)%R -> (t <= 1)%R ->
    {{ Pr[true] = ta_w }}
      $(ta_prog)
    {{ E[$(condition_pconstruct (ta_q t) (c_not ta_guard))]
         = $(t * t) * ta_w }}.
Proof.
  intros t H0 H1.
  unfold ta_prog.
  eapply HSeq with
    (eta2 := p_concentrated_mass (ta_regions 0) (PVar ta_w)).
  - eapply HConseq with
      (eta1 :=
         subst_bool_pformula ta_retry c_true
           (p_concentrated_mass (ta_regions 0) (PVar ta_w)))
      (eta2 := p_concentrated_mass (ta_regions 0) (PVar ta_w)).
    + intros ps Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [pterm_eval] in Hpre.
      unfold p_concentrated_mass, ta_regions, ta_guard.
      rewrite subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      apply psatisfies_p_and; split; apply psatisfies_p_eq;
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
           pconstruct_size subst_bool_cformula
             pterm_eval].
      * rewrite !bpv_eq_dec_refl; reflexivity.
      * exact Hpre.
    + apply HBoolAssign.
    + intros ps Hadm; cbn [psatisfies]; tauto.
  - replace (t * t)%R with (ta_solution t 0) by reflexivity.
    apply ta_loop_derivable; assumption.
Qed.
