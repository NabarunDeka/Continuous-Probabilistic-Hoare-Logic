(**
  HalfLaplaceRejection.v

  Program ([t3_prog b]):

      retry := tt;
      while retry do
        x <- sample(laplace(0, b));
        retry := (x < 0)
      end

  Triple ([t3_correct], for 0 <= t, 0 < b, and G such that the state-logic
  CDF formula [t3_cdf t b G] is valid):

      t3_cdf t b G :=
        Pr[tt] = 1  ->  E[ integral z ~ exponential(1/b), 1_(z <= t) ] = G

      { E[1_tt] = y }  t3_prog b  { E[1_(t <= x /\ ~retry)] = (1 - G) * y }

  Triple ([t3_terminates], for 0 < b):

      { E[1_tt] = y }  t3_prog b  { E[1_(0 <= x /\ ~retry)] = 1 * y }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import MeasureIntegration CdfLibraryFacts.
Require Import CdfAssertions.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * Small reusable facts *)

Lemma exp_le_compat :
  forall x y : R, (x <= y)%R -> (exp x <= exp y)%R.
Proof. exact exp_le_mono. Qed.

Lemma rpv_eq_dec_refl :
  forall (x : RealProgramVar) (A : Type) (a c : A),
    (if real_program_var_eq_dec x x then a else c) = a.
Proof.
  intros x A a c.
  destruct (real_program_var_eq_dec x x) as [_ | Hne];
    [reflexivity | contradiction].
Qed.

(** An expectation of a construct that is constant across states equals
    that constant on a normalized state. *)
Lemma t3_expect_const :
  forall (ps : Pstate) (q : PConstruct) (c : R),
    expectation (pstate_measure ps) (q_eval [[ indicator[true] ]]) = 1%R ->
    (forall v : state, q_eval q v = c) ->
    expectation (pstate_measure ps) (q_eval q) = c.
Proof.
  intros ps q c Hnorm Hval.
  rewrite (expect_const_construct _ _ c Hval), Hnorm; ring.
Qed.

(** * The program *)

Definition t3_x : RealProgramVar := real_program_var "t3_x".
Definition t3_z : RealProgramVar := real_program_var "t3_z".
Definition t3_retry : BoolProgramVar := bool_program_var "t3_retry".
Definition t3_y : ProbLogicVar := prob_logic_var "t3_y".

Definition t3_noise (b : R) : Distribution := <{ laplace(0, b) }>.

(** The rejection test: retry exactly when the draw was negative. *)
Definition t3_neg : CFormula := <{ t3_x < 0 }>.

(** The event whose probability we compute: the accepted draw is at least t. *)
Definition t3_tail (t : R) : CFormula := <{ t <= t3_x }>.

Definition t3_guard : CFormula := <{ t3_retry }>.

Definition t3_body (b : R) : Cmd :=
  <{ t3_x sample $(t3_noise b);
     t3_retry b= $(t3_neg) }>.

Definition t3_loop (b : R) : Cmd :=
  <{ while $(t3_guard) do $(t3_body b) end }>.

Definition t3_prog (b : R) : Cmd :=
  <{ t3_retry b= true; $(t3_loop b) }>.

(** The accepted mass above the threshold. *)
Definition t3_accepted (t : R) : PConstruct :=
  [[ indicator[$(t3_tail t) /\ ~ $(t3_guard)] ]].

(** * Certificate data.  One region: the guard itself.

    Half the mass is rejected each round; the exit reward is [r/2] with
    [r] a parameter (the probability that an [exponential(1/b)] sample
    exceeds [t]).  The solution is [r]. *)

Definition t3_regions (_ : nat) : CFormula := t3_guard.
Definition t3_transitions (_ _ : nat) : R := 1 / 2.
Definition t3_exits (r : R) (_ : nat) : R := r / 2.
Definition t3_solution (r : R) (_ : nat) : R := r.
Definition t3_q (t : R) : PConstruct := [[ indicator[$(t3_tail t)] ]].

Lemma t3_accepted_eq :
  forall t : R, condition_pconstruct (t3_q t) <{ ~ $(t3_guard) }> = t3_accepted t.
Proof. reflexivity. Qed.

(** * The two integrals produced by the sample *)

Lemma t3_integral_reject :
  forall (b : R) (v : state),
    (0 < b)%R ->
    q_eval [[ integral t3_x ~ $(t3_noise b), indicator[$(t3_neg)] ]] v = (1 / 2)%R.
Proof.
  intros b v Hb.
  rewrite <- (lap_below_zero_half b Hb).
  apply q_eval_laplace_indicator; [exact Hb |].
  intro r; unfold t3_neg, c_lt, c_not.
  cbn [satisfies]; rewrite update_real_same; cbn [term_eval].
  split; [intro H; apply Rnot_le_lt; exact H | intros H H'; lra].
Qed.

Lemma t3_integral_accept :
  forall (t b : R) (v : state),
    (0 <= t)%R -> (0 < b)%R ->
    q_eval
      [[ integral t3_x ~ $(t3_noise b),
         indicator[$(t3_tail t) /\ (~ $(t3_neg))] ]] v =
    lap_above 0 b t.
Proof.
  intros t b v Ht Hb.
  apply q_eval_laplace_indicator; [exact Hb |].
  intro r; unfold t3_tail, t3_neg, c_lt, c_and, c_not.
  cbn [satisfies]; rewrite !update_real_same; cbn [term_eval].
  split.
  - intro H.
    destruct (Rle_dec t r) as [Hz | Hz]; [exact Hz |].
    exfalso; apply H; intros Hle _; lra.
  - intros Hz Hf; apply (Hf Hz); intro Hneg; apply Hneg; lra.
Qed.

(** * The body premise

    The sample is fresh, so both expectations after it are constants:
    [1/2] for rejection and [r/2] for acceptance above [t]. *)

Lemma t3_body_step :
  forall t b r : R,
    (0 <= t)%R -> (0 < b)%R ->
    lap_above 0 b t = (r / 2)%R ->
    forall i : nat,
      (i < 1)%nat ->
      {{ $(p_concentrated_mass (t3_regions i) [[ 1 ]]) }}
        $(t3_body b)
      {{ $(while_body_post 1 t3_regions (t3_transitions i) t3_guard (t3_q t)
             (t3_exits r i)) }}.
Proof.
  intros t b r Ht Hb Hexit i Hi.
  unfold t3_body.
  eapply HSeq with
    (eta2 :=
       subst_bool_pformula t3_retry t3_neg
         (while_body_post 1 t3_regions (t3_transitions i) t3_guard (t3_q t)
            (t3_exits r i))).
  - apply HRealSample.
    + intros ps Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_and in Hpre.
      destruct Hpre as [_ Hmass].
      apply psatisfies_p_eq in Hmass.
      cbn [pterm_eval] in Hmass.
      unfold while_body_post, t3_q, t3_regions, t3_guard, t3_transitions,
        t3_exits.
      cbn [finite_p_and condition_pconstruct condition_pconstruct_fuel
           pconstruct_size].
      rewrite !subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      rewrite !sample_pformula_p_and, !sample_pformula_p_eq.
      apply psatisfies_p_and; split;
        [apply psatisfies_p_and; split | ].
      * apply psatisfies_p_true.
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
             pconstruct_size subst_bool_cformula].
        rewrite !bpv_eq_dec_refl.
        cbn [sample_pterm pterm_eval].
        rewrite (t3_expect_const ps _ (1 / 2)%R Hmass);
          [reflexivity | intro v; apply t3_integral_reject; exact Hb].
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
             pconstruct_size subst_bool_cformula t3_tail c_and c_not].
        rewrite !bpv_eq_dec_refl.
        cbn [sample_pterm pterm_eval].
        rewrite (t3_expect_const ps _ (r / 2)%R Hmass);
          [reflexivity | intro v; rewrite <- Hexit; apply t3_integral_accept; assumption].
    + intros ps Hadm _.
      refine (p_almost_sure_of_pointwise _ _ ps Hadm).
      intro v.
      unfold t3_noise.
      cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
      intro Hle; lra.
  - apply HBoolAssign.
Qed.

(** * The loop *)

Lemma t3_loop_derivable :
  forall t b r : R,
    (0 <= t)%R -> (0 < b)%R ->
    lap_above 0 b t = (r / 2)%R ->
    (0 < r <= 1)%R ->
    {{ $(p_concentrated_mass (t3_regions 0) [[ t3_y ]]) }}
      $(t3_loop b)
    {{ E[$(condition_pconstruct (t3_q t) <{ ~ $(t3_guard) }>)]
         = $(t3_solution r 0) * t3_y }}.
Proof.
  intros t b r Ht Hb Hexit Hr.
  eapply HWhile with
    (m := 1%nat) (k := 0%nat)
    (regions := t3_regions) (solution := t3_solution r)
    (exits := t3_exits r) (transitions := t3_transitions).
  - lia.
  - unfold while_regions_cover, cformula_valid, t3_regions.
    intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
  - unfold while_regions_in_guard, cformula_valid, t3_regions.
    intros i Hi v; cbn [satisfies]; tauto.
  - unfold while_regions_disjoint; intros i j Hi Hj; lia.
  - unfold while_progress, t3_exits.
    intros i Hi; left; lra.
  - intros i Hi; apply (t3_body_step t b r); assumption.
  - unfold while_solution, t3_solution, t3_transitions, t3_exits.
    intros i Hi; cbn [finite_r_sum]; split; lra.
Qed.

(** * The whole sampler, for a given exit rate *)

Lemma t3_prog_rate :
  forall t b r : R,
    (0 <= t)%R -> (0 < b)%R ->
    lap_above 0 b t = (r / 2)%R ->
    (0 < r <= 1)%R ->
    {{ Pr[true] = t3_y }}
      $(t3_prog b)
    {{ E[$(t3_accepted t)] = $(r) * t3_y }}.
Proof.
  intros t b r Ht Hb Hexit Hr.
  rewrite <- t3_accepted_eq.
  unfold t3_prog.
  eapply HSeq with
    (eta2 := p_concentrated_mass (t3_regions 0) (PVar t3_y)).
  - eapply HConseq with
      (eta1 :=
         subst_bool_pformula t3_retry c_true
           (p_concentrated_mass (t3_regions 0) (PVar t3_y)))
      (eta2 := p_concentrated_mass (t3_regions 0) (PVar t3_y)).
    + intros ps Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [pterm_eval] in Hpre.
      unfold p_concentrated_mass, t3_regions, t3_guard.
      rewrite subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      apply psatisfies_p_and; split; apply psatisfies_p_eq;
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
             pconstruct_size subst_bool_cformula pterm_eval].
      * rewrite !bpv_eq_dec_refl; reflexivity.
      * exact Hpre.
    + apply HBoolAssign.
    + intros ps Hadm; cbn [psatisfies]; tauto.
  - exact (t3_loop_derivable t b r Ht Hb Hexit Hr).
Qed.

(** * The CDF of the accepted value, as a state-logic formula

    [G] is the CDF at [t] of an [exponential(1/b)] sample, written as an
    integral of an indicator in the assertion logic. *)

Definition t3_cdf (t b G : R) : PFormula :=
  [[ Pr[true] = 1 ->
     E[ integral t3_z ~ exponential ( $((/ b)%R) ), indicator[t3_z <= $(t)] ] = $(G) ]].

(** Evaluating the CDF formula at a point mass pins [G] down. *)
Lemma t3_cdf_value :
  forall t b G : R,
    (0 <= t)%R -> (0 < b)%R ->
    pformula_valid (t3_cdf t b G) ->
    G = (1 - exp (- t / b))%R.
Proof.
  intros t b G Ht Hb Hvalid.
  set (ps0 := point_pstate demo_valuation).
  pose proof (Hvalid ps0 (point_admissible demo_valuation)) as H.
  unfold t3_cdf in H; cbn [psatisfies] in H.
  assert (Hone : psatisfies ps0 (p_eq (PExpect (QIndicator c_true)) (PConst 1))).
  { apply psatisfies_p_eq; cbn [pterm_eval]; unfold ps0.
    rewrite point_pstate_expect, q_eval_indicatorE.
    apply real_indicator_true; cbn [c_true satisfies]; tauto. }
  specialize (H Hone).
  apply psatisfies_p_eq in H; cbn [pterm_eval] in H.
  unfold ps0 in H.
  rewrite point_pstate_expect in H.
  rewrite (q_eval_exponential_indicator t3_z (/ b) _ (fun z => (z <= t)%R)) in H.
  - rewrite exp_atmost_closed in H.
    + rewrite <- H; f_equal; f_equal; field; lra.
    + apply Rinv_0_lt_compat; exact Hb.
    + exact Ht.
  - apply Rinv_0_lt_compat; exact Hb.
  - intro z; cbn [satisfies]; rewrite update_real_same; reflexivity.
Qed.

(** * The headline triple *)

Theorem t3_correct :
  forall t b G : R,
    (0 <= t)%R -> (0 < b)%R ->
    pformula_valid (t3_cdf t b G) ->
    {{ Pr[true] = t3_y }}
      $(t3_prog b)
    {{ E[$(t3_accepted t)] = $(1 - G) * t3_y }}.
Proof.
  intros t b G Ht Hb Hvalid.
  pose proof (t3_cdf_value t b G Ht Hb Hvalid) as HG.
  apply t3_prog_rate; [exact Ht | exact Hb | |].
  - rewrite lap_above_closed by assumption; rewrite HG; field.
  - rewrite HG; replace (1 - (1 - exp (- t / b)))%R with (exp (- t / b)) by ring.
    split; [apply exp_pos |].
    replace 1%R with (exp 0) by apply exp_0.
    apply exp_le_compat.
    assert (Hq : (0 <= t * / b)%R)
      by (apply Rmult_le_pos; [exact Ht | left; apply Rinv_0_lt_compat; exact Hb]).
    unfold Rdiv; lra.
Qed.

(** At [t = 0] the rate is one: the sampler terminates almost surely. *)
Corollary t3_terminates :
  forall b : R,
    (0 < b)%R ->
    {{ Pr[true] = t3_y }} $(t3_prog b) {{ E[$(t3_accepted 0)] = $(1%R) * t3_y }}.
Proof.
  intros b Hb.
  apply t3_prog_rate; [apply Rle_refl | exact Hb | | lra].
  rewrite lap_above_closed by (exact Hb || apply Rle_refl).
  replace (- 0 / b)%R with 0%R by (field; lra).
  rewrite exp_0; field.
Qed.
