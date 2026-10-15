(**
  TruncatedLaplaceRejection.v

  Program ([t4_prog mu b a c]):

      retry := tt;
      while retry do
        x <- sample(laplace(mu, b));
        retry := (x < a \/ c <= x)
      end

  Triple ([t4_correct], for 0 < b, a < t <= c, and Fa, Ft, Fc such that the
  state-logic CDF formulas [t4_cdf_rate mu b a Fa], [t4_cdf_rate mu b t Ft],
  [t4_cdf_rate mu b c Fc] are valid):

      t4_cdf_rate mu b u F :=
        Pr[tt] = 1  ->  E[ integral z ~ laplace(mu, b), 1_(z <= u) ] = F

      { E[1_tt] = y }
          t4_prog mu b a c
      { E[1_(x < t /\ ~retry)] = ((Ft - Fa) / (Fc - Fa)) * y }
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import MeasureIntegration.
Require Import CPHLFacts.CalculationFacts CPHLFacts.RealIntegrationFacts.
Require Import SampleBeforeLoop.
Require Import CdfLibraryFacts.
Require Import CdfAssertions.
Require Import HalfLaplaceRejection.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * Laplace masses of windows (real-level, used inside proofs only) *)

(** The Laplace mass of the half-open window [[lo, hi)]. *)
Definition lap_window (loc b lo hi : R) : R :=
  real_integral (fun z => lap_density loc b z * real_indicator (lo <= z < hi)).

Lemma lap_below_window :
  forall loc b lo hi : R,
    0 < b -> lo <= hi ->
    lap_below loc b hi = lap_below loc b lo + lap_window loc b lo hi.
Proof.
  intros loc b lo hi Hb Hlh.
  unfold lap_below, lap_window.
  rewrite <- real_integral_add.
  - apply real_integral_extensional; intro z.
    destruct (Rlt_dec z lo) as [Hz | Hz].
    + rewrite (real_indicator_true (z < hi)) by lra.
      rewrite (real_indicator_true (z < lo)) by lra.
      rewrite (real_indicator_false (lo <= z < hi)) by lra; ring.
    + rewrite (real_indicator_false (z < lo)) by lra.
      destruct (Rlt_dec z hi) as [Hh | Hh].
      * rewrite (real_indicator_true (z < hi)) by lra.
        rewrite (real_indicator_true (lo <= z < hi)) by lra; ring.
      * rewrite (real_indicator_false (z < hi)) by lra.
        rewrite (real_indicator_false (lo <= z < hi)) by lra; ring.
  - apply lap_masked_integrable; [exact Hb | apply real_measurable_below].
  - apply lap_masked_integrable; [exact Hb | apply real_measurable_between].
Qed.

(** The window mass as a difference of upper tails. *)
Lemma lap_window_above :
  forall loc b lo hi : R,
    0 < b -> lo <= hi ->
    lap_window loc b lo hi = lap_above loc b lo - lap_above loc b hi.
Proof.
  intros loc b lo hi Hb Hlh.
  pose proof (lap_below_window loc b lo hi Hb Hlh) as Hw.
  pose proof (lap_below_above loc b Hb lo) as Hlo.
  pose proof (lap_below_above loc b Hb hi) as Hhi.
  lra.
Qed.

Lemma lap_window_nonneg : forall loc b lo hi : R, 0 < b -> 0 <= lap_window loc b lo hi.
Proof.
  intros loc b lo hi Hb; unfold lap_window.
  apply real_integral_nonneg; intro z.
  apply Rmult_le_pos; [left; apply lap_density_pos; exact Hb |].
  unfold real_indicator; destruct (boolp.pselect (lo <= z < hi)); lra.
Qed.

(** A nonempty window has positive mass: on it the density is bounded below. *)
Lemma lap_window_pos : forall loc b lo hi : R, 0 < b -> lo < hi -> 0 < lap_window loc b lo hi.
Proof.
  intros loc b lo hi Hb Hlh.
  set (K := (1 / (2 * b)) * exp (- (Rabs (lo - loc) + (hi - lo)) / b)).
  assert (HK : 0 < K).
  { unfold K; apply Rmult_lt_0_compat; [apply Rdiv_lt_0_compat; lra | apply exp_pos]. }
  apply Rlt_le_trans with (K * real_integral_between lo hi (fun _ => 1)).
  { rewrite real_integral_between_one by lra.
    apply Rmult_lt_0_compat; [exact HK | lra]. }
  unfold real_integral_between.
  rewrite <- real_integral_scale by apply real_integrable_between_one.
  unfold lap_window; apply real_integral_le.
  - apply real_integrable_scale, real_integrable_between_one.
  - apply lap_masked_integrable; [exact Hb | apply real_measurable_between].
  - intro z; unfold real_indicator.
    destruct (boolp.pselect (lo <= z < hi)) as [Hin | Hout].
    + rewrite !Rmult_1_r; unfold K, lap_density.
      apply Rmult_le_compat_l; [left; apply Rdiv_lt_0_compat; lra |].
      apply exp_le_mono.
      unfold Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra |].
      apply Ropp_le_contravar.
      replace (z - loc) with ((lo - loc) + (z - lo)) by ring.
      eapply Rle_trans; [apply Rabs_triang |].
      rewrite (Rabs_right (z - lo)) by lra; lra.
    + rewrite Rmult_0_l, Rmult_0_r; lra.
Qed.

(** * The program *)

Definition t4_x : RealProgramVar := real_program_var "t4_x".
Definition t4_z : RealProgramVar := real_program_var "t4_z".
Definition t4_retry : BoolProgramVar := bool_program_var "t4_retry".
Definition t4_y : ProbLogicVar := prob_logic_var "t4_y".

Definition t4_noise (mu bb : R) : Distribution := <{ laplace(mu, bb) }>.

(** Reject when the draw falls outside the window [a, c). *)
Definition t4_reject (a c : R) : CFormula :=
  <{ (t4_x < a) \/ (c <= t4_x) }>.

Definition t4_below (t : R) : CFormula := <{ t4_x < t }>.

Definition t4_guard : CFormula := <{ t4_retry }>.

Definition t4_body (mu bb a c : R) : Cmd :=
  <{ t4_x sample $(t4_noise mu bb);
     t4_retry b= $(t4_reject a c) }>.

Definition t4_loop (mu bb a c : R) : Cmd :=
  <{ while $(t4_guard) do $(t4_body mu bb a c) end }>.

Definition t4_prog (mu bb a c : R) : Cmd :=
  <{ t4_retry b= true; $(t4_loop mu bb a c) }>.

(** The accepted mass below the threshold. *)
Definition t4_accepted (t : R) : PConstruct :=
  [[ indicator[$(t4_below t) /\ ~ $(t4_guard)] ]].

(** * Certificate data.  One region: the guard itself. *)

Definition t4_regions (_ : nat) : CFormula := t4_guard.
Definition t4_transitions (Fa Fc : R) (_ _ : nat) : R := 1 - (Fc - Fa).
Definition t4_exits (Fa Ft : R) (_ : nat) : R := Ft - Fa.
Definition t4_solution (Fa Fc Ft : R) (_ : nat) : R := (Ft - Fa) / (Fc - Fa).
Definition t4_q (t : R) : PConstruct := [[ indicator[$(t4_below t)] ]].

Lemma t4_accepted_eq :
  forall t : R, condition_pconstruct (t4_q t) <{ ~ $(t4_guard) }> = t4_accepted t.
Proof. reflexivity. Qed.

(** * The two integrals produced by the sample *)

Lemma t4_integral_reject :
  forall (mu bb a c : R) (v : state),
    0 < bb -> a <= c ->
    q_eval [[ integral t4_x ~ $(t4_noise mu bb), indicator[$(t4_reject a c)] ]] v =
    lap_below mu bb a + (1 - lap_below mu bb c).
Proof.
  intros mu bb a c v Hb Hac.
  rewrite (q_eval_laplace_indicator t4_x mu bb _ (fun z => z < a \/ c <= z)).
  - pose proof (lap_below_above mu bb Hb c) as Hc.
    replace (1 - lap_below mu bb c) with (lap_above mu bb c) by lra.
    unfold lap_below, lap_above.
    rewrite <- real_integral_add.
    + apply real_integral_extensional; intro z.
      destruct (Rlt_dec z a) as [Hz | Hz].
      * rewrite (real_indicator_true (z < a \/ c <= z)) by lra.
        rewrite (real_indicator_true (z < a)) by lra.
        rewrite (real_indicator_false (c <= z)) by lra; ring.
      * rewrite (real_indicator_false (z < a)) by lra.
        destruct (Rle_dec c z) as [Hcz | Hcz].
        -- rewrite (real_indicator_true (z < a \/ c <= z)) by lra.
           rewrite (real_indicator_true (c <= z)) by lra; ring.
        -- rewrite (real_indicator_false (z < a \/ c <= z)) by lra.
           rewrite (real_indicator_false (c <= z)) by lra; ring.
    + apply lap_masked_integrable; [exact Hb | apply real_measurable_below].
    + apply lap_masked_integrable; [exact Hb | apply real_measurable_above].
  - exact Hb.
  - intro r; unfold t4_reject, c_or, c_lt, c_not.
    cbn [satisfies]; rewrite !update_real_same; cbn [term_eval].
    split.
    + intro H; destruct (Rle_dec a r) as [Har | Har]; [right; apply H; intro Hf; exact (Hf Har) | left; lra].
    + intros [H | H] Hn; [exfalso; apply Hn; intro Har; lra | exact H].
Qed.

Lemma t4_integral_accept :
  forall (mu bb a c t : R) (v : state),
    0 < bb -> a <= t -> t <= c ->
    q_eval
      [[ integral t4_x ~ $(t4_noise mu bb),
         indicator[$(t4_below t) /\ (~ $(t4_reject a c))] ]] v =
    lap_below mu bb t - lap_below mu bb a.
Proof.
  intros mu bb a c t v Hb Hat Htc.
  rewrite (lap_below_window mu bb a t Hb Hat).
  replace (lap_below mu bb a + lap_window mu bb a t - lap_below mu bb a)
    with (lap_window mu bb a t) by ring.
  apply q_eval_laplace_indicator; [exact Hb |].
  intro r; unfold t4_below, t4_reject, c_and, c_or, c_lt, c_not.
  cbn [satisfies]; rewrite !update_real_same; cbn [term_eval].
  split.
  - intro H.
    destruct (Rle_dec t r) as [H1 | H1]; destruct (Rle_dec a r) as [H2 | H2];
      destruct (Rle_dec c r) as [H3 | H3];
      first [ split; lra | exfalso; lra | exfalso; apply H; tauto ].
  - intros [Har Hrt].
    assert (H1 : ~ t <= r) by lra.
    assert (H3 : ~ c <= r) by lra.
    tauto.
Qed.

(** * The CDF, as a state-logic formula *)

Definition t4_cdf_q (mu bb u : R) : PConstruct :=
  [[ integral t4_z ~ laplace ( $(mu), $(bb) ), indicator[t4_z <= $(u)] ]].

Definition t4_cdf_rate (mu bb u F : R) : PFormula :=
  [[ Pr[true] = 1 -> E[$(t4_cdf_q mu bb u)] = $(F) ]].

(** * Validity facts about the logic's terms (the oracle)

    These relate expectations of constructs to one another; real integrals
    appear only in their proofs. *)

Lemma t4_cdf_q_eval :
  forall (mu bb u : R) (v : state),
    0 < bb -> q_eval (t4_cdf_q mu bb u) v = lap_below mu bb u.
Proof.
  intros mu bb u v Hb.
  unfold t4_cdf_q.
  rewrite (q_eval_laplace_indicator t4_z mu bb _ (fun z => z <= u)).
  - exact (lap_atmost_below mu bb Hb u).
  - exact Hb.
  - intro z; cbn [satisfies]; rewrite update_real_same; reflexivity.
Qed.

Lemma t4_cdf_expect :
  forall (mu bb u : R) (ps : Pstate),
    0 < bb ->
    expectation (pstate_measure ps) (q_eval (t4_cdf_q mu bb u)) =
    lap_below mu bb u * expectation (pstate_measure ps) (q_eval (QIndicator c_true)).
Proof.
  intros mu bb u ps Hb.
  apply expect_const_construct; intro v; apply t4_cdf_q_eval; exact Hb.
Qed.

(** Rejection mass: everything outside [[a, c)]. *)
Lemma t4_reject_expect :
  forall (mu bb a c : R) (ps : Pstate),
    0 < bb -> a <= c ->
    expectation (pstate_measure ps)
      (q_eval [[ integral t4_x ~ $(t4_noise mu bb), indicator[$(t4_reject a c)] ]]) =
    expectation (pstate_measure ps) (q_eval (QIndicator c_true)) -
    expectation (pstate_measure ps) (q_eval (t4_cdf_q mu bb c)) +
    expectation (pstate_measure ps) (q_eval (t4_cdf_q mu bb a)).
Proof.
  intros mu bb a c ps Hb Hac.
  rewrite (expect_const_construct _ _ (lap_below mu bb a + (1 - lap_below mu bb c)))
    by (intro v; apply t4_integral_reject; assumption).
  rewrite !t4_cdf_expect by exact Hb.
  ring.
Qed.

(** Accepted mass below [t]: the window [[a, t)]. *)
Lemma t4_accept_expect :
  forall (mu bb a c t : R) (ps : Pstate),
    0 < bb -> a <= t -> t <= c ->
    expectation (pstate_measure ps)
      (q_eval [[ integral t4_x ~ $(t4_noise mu bb),
                 indicator[$(t4_below t) /\ (~ $(t4_reject a c))] ]]) =
    expectation (pstate_measure ps) (q_eval (t4_cdf_q mu bb t)) -
    expectation (pstate_measure ps) (q_eval (t4_cdf_q mu bb a)).
Proof.
  intros mu bb a c t ps Hb Hat Htc.
  rewrite (expect_const_construct _ _ (lap_below mu bb t - lap_below mu bb a))
    by (intro v; apply t4_integral_accept; assumption).
  rewrite !t4_cdf_expect by exact Hb.
  ring.
Qed.

(** The logic's CDF is strictly increasing on [[a, t]] and nondecreasing on
    [[t, c]], on unit-mass states. *)
Lemma t4_cdf_order_valid :
  forall mu bb a c t : R,
    0 < bb -> a < t -> t <= c ->
    pformula_valid
      [[ Pr[true] = 1 ->
         E[$(t4_cdf_q mu bb a)] < E[$(t4_cdf_q mu bb t)] /\
         E[$(t4_cdf_q mu bb t)] <= E[$(t4_cdf_q mu bb c)] ]].
Proof.
  intros mu bb a c t Hb Hat Htc ps Hadm; cbn [psatisfies]; intro Hm.
  apply psatisfies_p_eq in Hm; cbn [pterm_eval] in Hm.
  pose proof (lap_below_window mu bb a t Hb (Rlt_le _ _ Hat)) as Hat'.
  pose proof (lap_window_pos mu bb a t Hb Hat) as Hpos.
  pose proof (lap_below_window mu bb t c Hb Htc) as Htc'.
  pose proof (lap_window_nonneg mu bb t c Hb) as Hnn.
  apply psatisfies_p_and; split; cbn [psatisfies pterm_eval p_lt p_not];
    rewrite !t4_cdf_expect by exact Hb; rewrite Hm.
  - intro H; lra.
  - lra.
Qed.

(** The validity facts, read at the unit point mass, order the parameters. *)
Lemma t4_F_order :
  forall mu bb a c t Fa Fc Ft : R,
    0 < bb -> a < t -> t <= c ->
    pformula_valid (t4_cdf_rate mu bb a Fa) ->
    pformula_valid (t4_cdf_rate mu bb c Fc) ->
    pformula_valid (t4_cdf_rate mu bb t Ft) ->
    Fa < Ft /\ Ft <= Fc.
Proof.
  intros mu bb a c t Fa Fc Ft Hb Hat Htc Ha Hc Ht.
  pose proof (valid_at_point _ (t4_cdf_order_valid mu bb a c t Hb Hat Htc)) as Hr.
  cbn [psatisfies] in Hr; specialize (Hr point_unit_mass).
  apply psatisfies_p_and in Hr; destruct Hr as [H1 H2].
  cbn [psatisfies pterm_eval p_lt p_not] in H1, H2.
  pose proof point_unit_mass as Hm; apply psatisfies_p_eq in Hm; cbn [pterm_eval] in Hm.
  pose proof (point_admissible demo_valuation) as Hadm.
  rewrite (valid_unit_eq _ _ Fa Hadm Hm Ha), (valid_unit_eq _ _ Ft Hadm Hm Ht) in H1.
  rewrite (valid_unit_eq _ _ Ft Hadm Hm Ht), (valid_unit_eq _ _ Fc Hadm Hm Hc) in H2.
  split; [apply Rnot_le_lt; exact H1 | exact H2].
Qed.

(** * The body premise

    After the fresh sample, rejection has mass [1 - (Fc - Fa)] and acceptance
    below [t] has mass [Ft - Fa]: the CDF hypotheses are read at the current
    state. *)

Lemma t4_body_step :
  forall mu bb a c t Fa Fc Ft : R,
    0 < bb -> a <= t -> t <= c ->
    pformula_valid (t4_cdf_rate mu bb a Fa) ->
    pformula_valid (t4_cdf_rate mu bb c Fc) ->
    pformula_valid (t4_cdf_rate mu bb t Ft) ->
    forall i : nat,
      (i < 1)%nat ->
      {{ $(p_concentrated_mass (t4_regions i) [[ 1 ]]) }}
        $(t4_body mu bb a c)
      {{ $(while_body_post 1 t4_regions (t4_transitions Fa Fc i) t4_guard
             (t4_q t) (t4_exits Fa Ft i)) }}.
Proof.
  intros mu bb a c t Fa Fc Ft Hb Hat Htc Ha Hc Ht i Hi.
  assert (Hac : a <= c) by lra.
  unfold t4_body.
  eapply HSeq with
    (eta2 :=
       subst_bool_pformula t4_retry (t4_reject a c)
         (while_body_post 1 t4_regions (t4_transitions Fa Fc i) t4_guard
            (t4_q t) (t4_exits Fa Ft i))).
  - apply HRealSample.
    + intros ps Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_and in Hpre.
      destruct Hpre as [_ Hmass].
      apply psatisfies_p_eq in Hmass.
      cbn [pterm_eval] in Hmass.
      pose proof (valid_unit_eq ps _ Fa Hadm Hmass Ha) as HFa.
      pose proof (valid_unit_eq ps _ Fc Hadm Hmass Hc) as HFc.
      pose proof (valid_unit_eq ps _ Ft Hadm Hmass Ht) as HFt.
      unfold while_body_post, t4_q, t4_regions, t4_guard, t4_transitions,
        t4_exits.
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
        transitivity
          (expectation (pstate_measure ps) (q_eval (QIndicator c_true)) -
           expectation (pstate_measure ps) (q_eval (t4_cdf_q mu bb c)) +
           expectation (pstate_measure ps) (q_eval (t4_cdf_q mu bb a)));
          [exact (t4_reject_expect mu bb a c ps Hb Hac) | rewrite Hmass, HFa, HFc; ring].
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
             pconstruct_size subst_bool_cformula t4_below c_and c_not].
        rewrite !bpv_eq_dec_refl.
        cbn [sample_pterm pterm_eval].
        transitivity
          (expectation (pstate_measure ps) (q_eval (t4_cdf_q mu bb t)) -
           expectation (pstate_measure ps) (q_eval (t4_cdf_q mu bb a)));
          [exact (t4_accept_expect mu bb a c t ps Hb Hat Htc) | rewrite HFa, HFt; ring].
    + intros ps Hadm _.
      refine (p_almost_sure_of_pointwise _ _ ps Hadm).
      intro v.
      unfold t4_noise.
      cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
      intro Hle; lra.
  - apply HBoolAssign.
Qed.

(** * The loop *)

Lemma t4_loop_derivable :
  forall mu bb a c t Fa Fc Ft : R,
    0 < bb -> a < t -> t <= c ->
    pformula_valid (t4_cdf_rate mu bb a Fa) ->
    pformula_valid (t4_cdf_rate mu bb c Fc) ->
    pformula_valid (t4_cdf_rate mu bb t Ft) ->
    {{ $(p_concentrated_mass (t4_regions 0) [[ t4_y ]]) }}
      $(t4_loop mu bb a c)
    {{ E[$(condition_pconstruct (t4_q t) <{ ~ $(t4_guard) }>)]
         = $(t4_solution Fa Fc Ft 0) * t4_y }}.
Proof.
  intros mu bb a c t Fa Fc Ft Hb Hat Htc Ha Hc Ht.
  destruct (t4_F_order mu bb a c t Fa Fc Ft Hb Hat Htc Ha Hc Ht) as [Hn Hm].
  eapply HWhile with
    (m := 1%nat) (k := 0%nat)
    (regions := t4_regions) (solution := t4_solution Fa Fc Ft)
    (exits := t4_exits Fa Ft) (transitions := t4_transitions Fa Fc).
  - lia.
  - unfold while_regions_cover, cformula_valid, t4_regions.
    intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
  - unfold while_regions_in_guard, cformula_valid, t4_regions.
    intros i Hi v; cbn [satisfies]; tauto.
  - unfold while_regions_disjoint; intros i j Hi Hj; lia.
  - unfold while_progress, t4_exits.
    intros i Hi; left; lra.
  - intros i Hi; apply (t4_body_step mu bb a c t Fa Fc Ft); try assumption; lra.
  - unfold while_solution, t4_solution, t4_transitions, t4_exits.
    intros i Hi; cbn [finite_r_sum].
    split.
    + field; lra.
    + split.
      * unfold Rdiv; apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra].
      * apply (Rmult_le_reg_r (Fc - Fa)); [lra |].
        unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra.
Qed.

(** * The headline triple, with the CDF written in the logic *)

Theorem t4_correct :
  forall mu bb a c t Fa Fc Ft : R,
    0 < bb -> a < t -> t <= c ->
    pformula_valid (t4_cdf_rate mu bb a Fa) ->
    pformula_valid (t4_cdf_rate mu bb c Fc) ->
    pformula_valid (t4_cdf_rate mu bb t Ft) ->
    {{ Pr[true] = t4_y }}
      $(t4_prog mu bb a c)
    {{ E[$(t4_accepted t)] = $((Ft - Fa) / (Fc - Fa)) * t4_y }}.
Proof.
  intros mu bb a c t Fa Fc Ft Hb Hat Htc Ha Hc Ht.
  rewrite <- t4_accepted_eq.
  unfold t4_prog.
  eapply HSeq with
    (eta2 := p_concentrated_mass (t4_regions 0) (PVar t4_y)).
  - eapply HConseq with
      (eta1 :=
         subst_bool_pformula t4_retry c_true
           (p_concentrated_mass (t4_regions 0) (PVar t4_y)))
      (eta2 := p_concentrated_mass (t4_regions 0) (PVar t4_y)).
    + intros ps Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [pterm_eval] in Hpre.
      unfold p_concentrated_mass, t4_regions, t4_guard.
      rewrite subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      apply psatisfies_p_and; split; apply psatisfies_p_eq;
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
             pconstruct_size subst_bool_cformula pterm_eval].
      * rewrite !bpv_eq_dec_refl; reflexivity.
      * exact Hpre.
    + apply HBoolAssign.
    + intros ps Hadm; cbn [psatisfies]; tauto.
  - exact (t4_loop_derivable mu bb a c t Fa Fc Ft Hb Hat Htc Ha Hc Ht).
Qed.
