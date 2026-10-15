(**
  NoisyThresholdMonitor.v

  Program ([ntm_prog mu b a c]):

      left := ff;
      active := tt;
      while active do
        x <- sample(laplace(mu, b));
        left := (x < a);
        active := (a <= x /\ x < c)
      end

  CDF formula ([ntm_cdf mu b u F]):

      Pr[tt] = 1  ->  E[ integral z ~ laplace(mu, b), 1_(z <= u) ] = F

  Triple ([ntm_left_probability], for 0 < b, a <= c, and Fa, Fc such that
  [ntm_cdf mu b a Fa] and [ntm_cdf mu b c Fc] are valid):

      { E[1_tt] = y }  ntm_prog mu b a c
      { E[1_(left /\ ~active)] = (Fa / (Fa + (1 - Fc))) * y }

  Triple ([ntm_right_probability], same hypotheses):

      { E[1_tt] = y }  ntm_prog mu b a c
      { E[1_(~left /\ ~active)] = ((1 - Fc) / (Fa + (1 - Fc))) * y }
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
Require Import CPHLFacts.CalculationFacts.
Require Import CdfAssertions.
Require Import HalfLaplaceRejection.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * Local helpers *)

Lemma ntm_satisfies_c_and :
  forall (v : state) (g1 g2 : CFormula),
    satisfies v <{ $(g1) /\ $(g2) }> <-> (satisfies v g1 /\ satisfies v g2).
Proof.
  intros v g1 g2.
  cbn [c_and c_not satisfies].
  split.
  - intro H.
    destruct (classic (satisfies v g1)) as [H1 | H1].
    + destruct (classic (satisfies v g2)) as [H2 | H2].
      * split; assumption.
      * exfalso; apply H; intros _ H2'; contradiction.
    + exfalso; apply H; intro H1'; contradiction.
  - intros [H1 H2] Hf; exact (Hf H1 H2).
Qed.

(** * The program *)

Definition ntm_x : RealProgramVar := real_program_var "ntm_x".
Definition ntm_z : RealProgramVar := real_program_var "ntm_z".
Definition ntm_active : BoolProgramVar := bool_program_var "ntm_active".
Definition ntm_left : BoolProgramVar := bool_program_var "ntm_left".
Definition ntm_y : ProbLogicVar := prob_logic_var "ntm_y".

Definition ntm_noise (mu bb : R) : Distribution := <{ laplace(mu, bb) }>.

Definition ntm_below (u : R) : CFormula := <{ ntm_x < u }>.

Definition ntm_above (u : R) : CFormula := <{ u <= ntm_x }>.

(** Stay active exactly while the reading is inside the band. *)
Definition ntm_inside (a c : R) : CFormula :=
  <{ $(ntm_above a) /\ $(ntm_below c) }>.

Definition ntm_guard : CFormula := <{ ntm_active }>.

Definition ntm_body (mu bb a c : R) : Cmd :=
  <{ ntm_x      sample $(ntm_noise mu bb);
     ntm_left   b= $(ntm_below a);
     ntm_active b= $(ntm_inside a c) }>.

Definition ntm_loop (mu bb a c : R) : Cmd :=
  <{ while $(ntm_guard) do $(ntm_body mu bb a c) end }>.

(** [left] is initialised first so that, working backwards, the
    substitution reaching [active] is the reflexive one. *)
Definition ntm_prog (mu bb a c : R) : Cmd :=
  <{ ntm_left   b= false;
     ntm_active b= true;
     $(ntm_loop mu bb a c) }>.

(** The two reported events. *)
Definition ntm_reported_left : PConstruct :=
  [[ indicator[ntm_left /\ ~ $(ntm_guard)] ]].
Definition ntm_reported_right : PConstruct :=
  [[ indicator[(~ ntm_left) /\ ~ $(ntm_guard)] ]].

(** * Satisfaction of the atomic formulas, after a sample *)

Lemma ntm_sat_below :
  forall (u z : R) (v : state),
    satisfies (update_real v ntm_x z) (ntm_below u) <-> (z < u)%R.
Proof.
  intros u z v.
  unfold ntm_below, c_lt, c_not.
  cbn [satisfies]; rewrite update_real_same; cbn [term_eval].
  split.
  - intro H.
    destruct (Rlt_dec z u) as [Hd | Hd]; [exact Hd |].
    exfalso; apply H; lra.
  - intros Hz Hcontra; lra.
Qed.

Lemma ntm_sat_above :
  forall (u z : R) (v : state),
    satisfies (update_real v ntm_x z) (ntm_above u) <-> (u <= z)%R.
Proof.
  intros u z v.
  unfold ntm_above.
  cbn [satisfies]; rewrite update_real_same; cbn [term_eval].
  split; intro H; exact H.
Qed.

Lemma ntm_sat_inside :
  forall (a c z : R) (v : state),
    satisfies (update_real v ntm_x z) (ntm_inside a c) <->
    ((a <= z)%R /\ (z < c)%R).
Proof.
  intros a c z v.
  unfold ntm_inside.
  rewrite ntm_satisfies_c_and, ntm_sat_above, ntm_sat_below.
  split; intro H; exact H.
Qed.

Lemma ntm_sat_left_exit :
  forall (a c z : R) (v : state),
    (a <= c)%R ->
    satisfies (update_real v ntm_x z)
      <{ $(ntm_below a) /\ (~ $(ntm_inside a c)) }> <-> (z < a)%R.
Proof.
  intros a c z v Hac.
  rewrite ntm_satisfies_c_and.
  cbn [c_not satisfies].
  rewrite ntm_sat_below.
  split.
  - intros [Hz _]; exact Hz.
  - intro Hz; split; [exact Hz |].
    intro Hin; apply ntm_sat_inside in Hin; lra.
Qed.

Lemma ntm_sat_right_exit :
  forall (a c z : R) (v : state),
    (a <= c)%R ->
    satisfies (update_real v ntm_x z)
      <{ (~ $(ntm_below a)) /\ (~ $(ntm_inside a c)) }> <-> (c <= z)%R.
Proof.
  intros a c z v Hac.
  rewrite ntm_satisfies_c_and.
  cbn [c_not satisfies].
  split.
  - intros [Hnb Hni].
    assert (Ha : (a <= z)%R).
    { destruct (Rle_dec a z) as [Hd | Hd]; [exact Hd |].
      exfalso; apply Hnb; apply ntm_sat_below; lra. }
    destruct (Rle_dec c z) as [Hd | Hd]; [exact Hd |].
    exfalso; apply Hni; apply ntm_sat_inside; split; lra.
  - intro Hcz.
    split.
    + intro Hb; apply ntm_sat_below in Hb; lra.
    + intro Hin; apply ntm_sat_inside in Hin; lra.
Qed.

(** * Laplace masses of the three regions

    The line splits into [z < a], [a <= z < c] and [c <= z]. *)

Lemma ntm_lap_split :
  forall mu bb a c : R,
    (0 < bb)%R -> (a <= c)%R ->
    real_integral
      (fun z => lap_density mu bb z * real_indicator ((a <= z)%R /\ (z < c)%R)) =
    (1 - lap_below mu bb a - lap_above mu bb c)%R.
Proof.
  intros mu bb a c Hb Hac.
  pose proof (lap_below_above mu bb Hb a) as Htot.
  assert (Hsplit :
    lap_above mu bb a =
    (real_integral
       (fun z => lap_density mu bb z * real_indicator ((a <= z)%R /\ (z < c)%R)) +
     lap_above mu bb c)%R).
  { unfold lap_above.
    rewrite <- real_integral_add.
    - apply real_integral_extensional; intro z.
      destruct (Rlt_dec z a) as [Hza | Hza].
      + rewrite (real_indicator_false (a <= z)%R) by lra.
        rewrite (real_indicator_false ((a <= z)%R /\ (z < c)%R)) by lra.
        rewrite (real_indicator_false (c <= z)%R) by lra; ring.
      + rewrite (real_indicator_true (a <= z)%R) by lra.
        destruct (Rlt_dec z c) as [Hzc | Hzc].
        * rewrite (real_indicator_true ((a <= z)%R /\ (z < c)%R)) by lra.
          rewrite (real_indicator_false (c <= z)%R) by lra; ring.
        * rewrite (real_indicator_false ((a <= z)%R /\ (z < c)%R)) by lra.
          rewrite (real_indicator_true (c <= z)%R) by lra; ring.
    - apply lap_masked_integrable; [exact Hb | apply real_measurable_between].
    - apply lap_masked_integrable; [exact Hb | apply real_measurable_above]. }
  lra.
Qed.

(** Every lower tail has positive mass: on [c-1, c) the density is bounded
    below by a positive constant. *)
Lemma ntm_lap_below_pos :
  forall mu bb c : R, (0 < bb)%R -> (0 < lap_below mu bb c)%R.
Proof.
  intros mu bb c Hb.
  set (K := ((1 / (2 * bb)) * exp (- (Rabs (c - mu) + 1) / bb))%R).
  assert (HK : (0 < K)%R).
  { unfold K; apply Rmult_lt_0_compat; [apply Rdiv_lt_0_compat; lra | apply exp_pos]. }
  apply Rlt_le_trans with (K * real_integral_between (c - 1) c (fun _ => 1))%R.
  { rewrite real_integral_between_one by lra.
    replace (c - (c - 1))%R with 1%R by ring; lra. }
  unfold real_integral_between.
  rewrite <- real_integral_scale by apply real_integrable_between_one.
  unfold lap_below; apply real_integral_le.
  - apply real_integrable_scale, real_integrable_between_one.
  - apply lap_masked_integrable; [exact Hb | apply real_measurable_below].
  - intro z; unfold real_indicator.
    destruct (boolp.pselect ((c - 1 <= z)%R /\ (z < c)%R)) as [Hin | Hout];
      destruct (boolp.pselect (z < c)%R) as [Hz | Hz].
    + rewrite !Rmult_1_r; unfold K, lap_density.
      apply Rmult_le_compat_l; [left; apply Rdiv_lt_0_compat; lra |].
      apply exp_le_mono.
      unfold Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra |].
      apply Ropp_le_contravar.
      replace (z - mu)%R with ((c - mu) + (z - c))%R by ring.
      eapply Rle_trans; [apply Rabs_triang |].
      rewrite (Rabs_left1 (z - c)) by lra; lra.
    + lra.
    + pose proof (lap_density_pos mu bb Hb z); lra.
    + lra.
Qed.

(** * The three integrals produced by the sample *)

Lemma ntm_integral_inside :
  forall (mu bb a c : R) (v : state),
    (0 < bb)%R -> (a <= c)%R ->
    q_eval
      [[ integral ntm_x ~ $(ntm_noise mu bb),
         indicator[$(ntm_inside a c)] ]] v =
    (1 - lap_below mu bb a - lap_above mu bb c)%R.
Proof.
  intros mu bb a c v Hb Hac.
  rewrite <- (ntm_lap_split mu bb a c Hb Hac).
  apply q_eval_laplace_indicator; [exact Hb |].
  intro r; apply ntm_sat_inside.
Qed.

Lemma ntm_integral_left :
  forall (mu bb a c : R) (v : state),
    (0 < bb)%R -> (a <= c)%R ->
    q_eval
      [[ integral ntm_x ~ $(ntm_noise mu bb),
         indicator[$(ntm_below a) /\ (~ $(ntm_inside a c))] ]] v =
    lap_below mu bb a.
Proof.
  intros mu bb a c v Hb Hac.
  apply q_eval_laplace_indicator; [exact Hb |].
  intro r; apply ntm_sat_left_exit; exact Hac.
Qed.

Lemma ntm_integral_right :
  forall (mu bb a c : R) (v : state),
    (0 < bb)%R -> (a <= c)%R ->
    q_eval
      [[ integral ntm_x ~ $(ntm_noise mu bb),
         indicator[(~ $(ntm_below a)) /\ (~ $(ntm_inside a c))] ]] v =
    lap_above mu bb c.
Proof.
  intros mu bb a c v Hb Hac.
  apply q_eval_laplace_indicator; [exact Hb |].
  intro r; apply ntm_sat_right_exit; exact Hac.
Qed.

(** * The Laplace CDF, as a state-logic formula *)

Definition ntm_cdf_q (mu bb u : R) : PConstruct :=
  [[ integral ntm_z ~ laplace ( $(mu), $(bb) ), indicator[ntm_z <= $(u)] ]].

Definition ntm_cdf (mu bb u F : R) : PFormula :=
  [[ Pr[true] = 1 -> E[$(ntm_cdf_q mu bb u)] = $(F) ]].

(** * Validity facts about the logic's terms (the oracle)

    These relate expectations of constructs to one another; real integrals
    appear only in their proofs. *)

Lemma ntm_cdf_q_eval :
  forall (mu bb u : R) (v : state),
    (0 < bb)%R -> q_eval (ntm_cdf_q mu bb u) v = lap_below mu bb u.
Proof.
  intros mu bb u v Hb.
  unfold ntm_cdf_q.
  rewrite (q_eval_laplace_indicator ntm_z mu bb _ (fun z => (z <= u)%R)).
  - exact (lap_atmost_below mu bb Hb u).
  - exact Hb.
  - intro z; cbn [satisfies]; rewrite update_real_same; reflexivity.
Qed.

Lemma ntm_cdf_expect :
  forall (mu bb u : R) (ps : Pstate),
    (0 < bb)%R ->
    expectation (pstate_measure ps) (q_eval (ntm_cdf_q mu bb u)) =
    (lap_below mu bb u * expectation (pstate_measure ps) (q_eval (QIndicator c_true)))%R.
Proof.
  intros mu bb u ps Hb.
  apply expect_const_construct; intro v; apply ntm_cdf_q_eval; exact Hb.
Qed.

Lemma ntm_inside_expect :
  forall (mu bb a c : R) (ps : Pstate),
    (0 < bb)%R -> (a <= c)%R ->
    expectation (pstate_measure ps)
      (q_eval [[ integral ntm_x ~ $(ntm_noise mu bb), indicator[$(ntm_inside a c)] ]]) =
    (expectation (pstate_measure ps) (q_eval (ntm_cdf_q mu bb c)) -
     expectation (pstate_measure ps) (q_eval (ntm_cdf_q mu bb a)))%R.
Proof.
  intros mu bb a c ps Hb Hac.
  rewrite (expect_const_construct _ _ (1 - lap_below mu bb a - lap_above mu bb c))
    by (intro v; apply ntm_integral_inside; assumption).
  rewrite !ntm_cdf_expect by exact Hb.
  pose proof (lap_below_above mu bb Hb c) as Hs.
  replace (lap_above mu bb c) with (1 - lap_below mu bb c)%R by lra.
  ring.
Qed.

Lemma ntm_left_expect :
  forall (mu bb a c : R) (ps : Pstate),
    (0 < bb)%R -> (a <= c)%R ->
    expectation (pstate_measure ps)
      (q_eval [[ integral ntm_x ~ $(ntm_noise mu bb),
                 indicator[$(ntm_below a) /\ (~ $(ntm_inside a c))] ]]) =
    expectation (pstate_measure ps) (q_eval (ntm_cdf_q mu bb a)).
Proof.
  intros mu bb a c ps Hb Hac.
  rewrite (expect_const_construct _ _ (lap_below mu bb a))
    by (intro v; apply ntm_integral_left; assumption).
  rewrite ntm_cdf_expect by exact Hb.
  reflexivity.
Qed.

Lemma ntm_right_expect :
  forall (mu bb a c : R) (ps : Pstate),
    (0 < bb)%R -> (a <= c)%R ->
    expectation (pstate_measure ps)
      (q_eval [[ integral ntm_x ~ $(ntm_noise mu bb),
                 indicator[(~ $(ntm_below a)) /\ (~ $(ntm_inside a c))] ]]) =
    (expectation (pstate_measure ps) (q_eval (QIndicator c_true)) -
     expectation (pstate_measure ps) (q_eval (ntm_cdf_q mu bb c)))%R.
Proof.
  intros mu bb a c ps Hb Hac.
  rewrite (expect_const_construct _ _ (lap_above mu bb c))
    by (intro v; apply ntm_integral_right; assumption).
  rewrite ntm_cdf_expect by exact Hb.
  pose proof (lap_below_above mu bb Hb c) as Hs.
  replace (lap_above mu bb c) with (1 - lap_below mu bb c)%R by lra.
  ring.
Qed.

(** On unit-mass states the logic's CDF is positive at [a] and below one at
    [c]. *)
Lemma ntm_cdf_range_valid :
  forall mu bb a c : R,
    (0 < bb)%R ->
    pformula_valid
      [[ Pr[true] = 1 ->
         0 < E[$(ntm_cdf_q mu bb a)] /\ E[$(ntm_cdf_q mu bb c)] < 1 ]].
Proof.
  intros mu bb a c Hb ps Hadm; cbn [psatisfies]; intro Hm.
  apply psatisfies_p_eq in Hm; cbn [pterm_eval] in Hm.
  pose proof (ntm_lap_below_pos mu bb a Hb) as Hpa.
  pose proof (lap_above_pos mu bb Hb c) as Hpc.
  pose proof (lap_below_above mu bb Hb c) as Hs.
  apply psatisfies_p_and; split; cbn [psatisfies pterm_eval p_lt p_not];
    rewrite !ntm_cdf_expect by exact Hb; rewrite Hm.
  - intro H; lra.
  - intro H; lra.
Qed.

(** The validity facts, read at the unit point mass, bound the parameters. *)
Lemma ntm_F_range :
  forall mu bb a c Fa Fc : R,
    (0 < bb)%R ->
    pformula_valid (ntm_cdf mu bb a Fa) ->
    pformula_valid (ntm_cdf mu bb c Fc) ->
    (0 < Fa)%R /\ (Fc < 1)%R.
Proof.
  intros mu bb a c Fa Fc Hb Ha Hc.
  pose proof (valid_at_point _ (ntm_cdf_range_valid mu bb a c Hb)) as Hr.
  cbn [psatisfies] in Hr; specialize (Hr point_unit_mass).
  apply psatisfies_p_and in Hr; destruct Hr as [H1 H2].
  cbn [psatisfies pterm_eval p_lt p_not] in H1, H2.
  pose proof point_unit_mass as Hm; apply psatisfies_p_eq in Hm; cbn [pterm_eval] in Hm.
  pose proof (point_admissible demo_valuation) as Hadm.
  rewrite (valid_unit_eq _ _ Fa Hadm Hm Ha) in H1.
  rewrite (valid_unit_eq _ _ Fc Hadm Hm Hc) in H2.
  split; apply Rnot_le_lt; assumption.
Qed.

(** * Certificate data

    One region: the guard itself.  The exit masses are [Fa] (left) and
    [1 - Fc] (right); the mass that stays in the band is [Fc - Fa]. *)

Definition ntm_regions (_ : nat) : CFormula := ntm_guard.

Definition ntm_transitions (pL pR : R) (_ _ : nat) : R := (1 - pL - pR)%R.

Definition ntm_exit (p : R) (_ : nat) : R := p.

Definition ntm_sol (p pL pR : R) (_ : nat) : R := (p / (pL + pR))%R.

Definition ntm_q_left : PConstruct := [[ indicator[ntm_left] ]].
Definition ntm_q_right : PConstruct := [[ indicator[~ ntm_left] ]].

Lemma ntm_reported_left_eq :
  condition_pconstruct ntm_q_left (c_not ntm_guard) = ntm_reported_left.
Proof. reflexivity. Qed.

Lemma ntm_reported_right_eq :
  condition_pconstruct ntm_q_right (c_not ntm_guard) = ntm_reported_right.
Proof. reflexivity. Qed.

(** * The body premise, for either exit event

    [q] selects the exit event and [p] is its post-sample expectation on
    unit-mass states.  The band mass is read off the CDF hypotheses. *)

Lemma ntm_body_step :
  forall (mu bb a c Fa Fc p : R) (q : PConstruct),
    (0 < bb)%R -> (a <= c)%R ->
    pformula_valid (ntm_cdf mu bb a Fa) ->
    pformula_valid (ntm_cdf mu bb c Fc) ->
    pformula_valid
      [[ Pr[true] = 1 ->
         $(sample_pterm ntm_x (ntm_noise mu bb)
             (subst_bool_pterm ntm_left (ntm_below a)
                (subst_bool_pterm ntm_active (ntm_inside a c)
                   (PExpect (condition_pconstruct q (c_not ntm_guard)))))) = $(p) ]] ->
    forall i : nat,
      (i < 1)%nat ->
      {{ $(p_concentrated_mass (ntm_regions i) [[ 1 ]]) }}
        $(ntm_body mu bb a c)
      {{ $(while_body_post 1 ntm_regions (ntm_transitions Fa (1 - Fc) i)
             ntm_guard q (ntm_exit p i)) }}.
Proof.
  intros mu bb a c Fa Fc p q Hb Hac Ha Hc Hexit i Hi.
  unfold ntm_body.
  eapply HSeq with
    (eta2 :=
       subst_bool_pformula ntm_left (ntm_below a)
         (subst_bool_pformula ntm_active (ntm_inside a c)
            (while_body_post 1 ntm_regions (ntm_transitions Fa (1 - Fc) i)
               ntm_guard q (ntm_exit p i)))).
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
      unfold while_body_post, ntm_regions, ntm_transitions, ntm_exit.
      cbn [finite_p_and].
      rewrite !subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      rewrite !sample_pformula_p_and, !sample_pformula_p_eq.
      apply psatisfies_p_and; split; [apply psatisfies_p_and; split | ].
      * apply psatisfies_p_true.
      * apply psatisfies_p_eq.
        unfold ntm_guard.
        cbn [condition_pconstruct condition_pconstruct_fuel pconstruct_size
             subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
             subst_bool_cformula].
        rewrite !bpv_eq_dec_refl.
        cbn [sample_pterm pterm_eval].
        transitivity
          (expectation (pstate_measure ps) (q_eval (ntm_cdf_q mu bb c)) -
           expectation (pstate_measure ps) (q_eval (ntm_cdf_q mu bb a)))%R;
          [exact (ntm_inside_expect mu bb a c ps Hb Hac) | rewrite HFa, HFc; ring].
      * pose proof (Hexit ps Hadm) as He; cbn [psatisfies] in He.
        assert (Hone : psatisfies ps (p_eq (PExpect (QIndicator c_true)) (PConst 1)))
          by (apply psatisfies_p_eq; cbn [pterm_eval]; exact Hmass).
        specialize (He Hone); apply psatisfies_p_eq in He; cbn [pterm_eval] in He.
        apply psatisfies_p_eq; cbn [pterm_eval]; exact He.
    + intros ps Hadm _.
      refine (p_almost_sure_of_pointwise _ _ ps Hadm).
      intro v.
      unfold ntm_noise.
      cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
      intro Hle; lra.
  - eapply HSeq with
      (eta2 :=
         subst_bool_pformula ntm_active (ntm_inside a c)
           (while_body_post 1 ntm_regions (ntm_transitions Fa (1 - Fc) i)
              ntm_guard q (ntm_exit p i)));
      apply HBoolAssign.
Qed.

Lemma ntm_body_left :
  forall mu bb a c Fa Fc : R,
    (0 < bb)%R -> (a <= c)%R ->
    pformula_valid (ntm_cdf mu bb a Fa) ->
    pformula_valid (ntm_cdf mu bb c Fc) ->
    forall i : nat,
      (i < 1)%nat ->
      {{ $(p_concentrated_mass (ntm_regions i) [[ 1 ]]) }}
        $(ntm_body mu bb a c)
      {{ $(while_body_post 1 ntm_regions (ntm_transitions Fa (1 - Fc) i)
             ntm_guard ntm_q_left (ntm_exit Fa i)) }}.
Proof.
  intros mu bb a c Fa Fc Hb Hac Ha Hc.
  apply ntm_body_step; try assumption.
  intros ps Hadm; cbn [psatisfies]; intro Hm.
  apply psatisfies_p_eq in Hm; cbn [pterm_eval] in Hm.
  rename Hm into Hmass.
  apply psatisfies_p_eq; cbn [pterm_eval].
  unfold ntm_q_left, ntm_guard.
  cbn [condition_pconstruct condition_pconstruct_fuel pconstruct_size
       subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
       subst_bool_cformula c_and c_not].
  rewrite !bpv_eq_dec_refl.
  cbn [sample_pterm pterm_eval].
  transitivity (expectation (pstate_measure ps) (q_eval (ntm_cdf_q mu bb a)));
    [exact (ntm_left_expect mu bb a c ps Hb Hac) |].
  exact (valid_unit_eq ps _ Fa Hadm Hmass Ha).
Qed.

Lemma ntm_body_right :
  forall mu bb a c Fa Fc : R,
    (0 < bb)%R -> (a <= c)%R ->
    pformula_valid (ntm_cdf mu bb a Fa) ->
    pformula_valid (ntm_cdf mu bb c Fc) ->
    forall i : nat,
      (i < 1)%nat ->
      {{ $(p_concentrated_mass (ntm_regions i) [[ 1 ]]) }}
        $(ntm_body mu bb a c)
      {{ $(while_body_post 1 ntm_regions (ntm_transitions Fa (1 - Fc) i)
             ntm_guard ntm_q_right (ntm_exit (1 - Fc) i)) }}.
Proof.
  intros mu bb a c Fa Fc Hb Hac Ha Hc.
  apply ntm_body_step; try assumption.
  intros ps Hadm; cbn [psatisfies]; intro Hm.
  apply psatisfies_p_eq in Hm; cbn [pterm_eval] in Hm.
  rename Hm into Hmass.
  apply psatisfies_p_eq; cbn [pterm_eval].
  unfold ntm_q_right, ntm_guard.
  cbn [condition_pconstruct condition_pconstruct_fuel pconstruct_size
       subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
       subst_bool_cformula c_and c_not].
  rewrite !bpv_eq_dec_refl.
  cbn [sample_pterm pterm_eval].
  transitivity
    (expectation (pstate_measure ps) (q_eval (QIndicator c_true)) -
     expectation (pstate_measure ps) (q_eval (ntm_cdf_q mu bb c)))%R;
    [exact (ntm_right_expect mu bb a c ps Hb Hac) |].
  rewrite Hmass, (valid_unit_eq ps _ Fc Hadm Hmass Hc); reflexivity.
Qed.

(** * The loop, for either exit event *)

Lemma ntm_loop_derivable :
  forall (mu bb a c pL pR p : R) (q : PConstruct),
    (0 < pL)%R -> (0 < pR)%R -> (0 < p)%R -> (p <= pL + pR)%R ->
    (forall i : nat,
       (i < 1)%nat ->
       {{ $(p_concentrated_mass (ntm_regions i) [[ 1 ]]) }}
         $(ntm_body mu bb a c)
       {{ $(while_body_post 1 ntm_regions (ntm_transitions pL pR i)
              ntm_guard q (ntm_exit p i)) }}) ->
    {{ $(p_concentrated_mass (ntm_regions 0) [[ ntm_y ]]) }}
      $(ntm_loop mu bb a c)
    {{ E[$(condition_pconstruct q <{ ~ $(ntm_guard) }>)]
         = $(ntm_sol p pL pR 0) * ntm_y }}.
Proof.
  intros mu bb a c pL pR p q HpL HpR Hp Hle Hbody.
  eapply HWhile with
    (m := 1%nat) (k := 0%nat)
    (regions := ntm_regions) (solution := ntm_sol p pL pR)
    (exits := ntm_exit p) (transitions := ntm_transitions pL pR).
  - lia.
  - unfold while_regions_cover, cformula_valid, ntm_regions.
    intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
  - unfold while_regions_in_guard, cformula_valid, ntm_regions.
    intros i Hi v; cbn [satisfies]; tauto.
  - unfold while_regions_disjoint; intros i j Hi Hj; lia.
  - unfold while_progress, ntm_exit.
    intros i Hi; left; exact Hp.
  - exact Hbody.
  - unfold while_solution, ntm_sol, ntm_transitions, ntm_exit.
    intros i Hi.
    cbn [finite_r_sum].
    split.
    + field; lra.
    + split.
      * unfold Rdiv; apply Rmult_le_pos; [lra |].
        left; apply Rinv_0_lt_compat; lra.
      * apply Rmult_le_reg_r with (r := (pL + pR)%R); [lra |].
        replace (p / (pL + pR) * (pL + pR))%R with p by (field; lra).
        lra.
Qed.

(** * The prefix concentrates all mass on the single region. *)

Lemma ntm_prefix :
  forall (mu bb a c : R) (theta : PFormula),
    {{ $(p_concentrated_mass (ntm_regions 0) [[ ntm_y ]]) }}
      $(ntm_loop mu bb a c)
    {{ $(theta) }} ->
    {{ Pr[true] = ntm_y }}
      $(ntm_prog mu bb a c)
    {{ $(theta) }}.
Proof.
  intros mu bb a c theta Hloop.
  unfold ntm_prog.
  eapply HSeq with
    (eta2 :=
       subst_bool_pformula ntm_active c_true
         (p_concentrated_mass (ntm_regions 0) (PVar ntm_y))).
  - eapply HConseq with
      (eta1 :=
         subst_bool_pformula ntm_left FFalse
           (subst_bool_pformula ntm_active c_true
              (p_concentrated_mass (ntm_regions 0) (PVar ntm_y))))
      (eta2 :=
         subst_bool_pformula ntm_active c_true
           (p_concentrated_mass (ntm_regions 0) (PVar ntm_y))).
    + intros ps Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [pterm_eval] in Hpre.
      unfold p_concentrated_mass, ntm_regions, ntm_guard.
      rewrite !subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      apply psatisfies_p_and; split; apply psatisfies_p_eq;
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_pconstruct_fuel
             pconstruct_size subst_bool_cformula pterm_eval].
      * rewrite !bpv_eq_dec_refl.
        destruct (bool_program_var_eq_dec ntm_active ntm_left) as [Heq | _];
          [discriminate Heq | reflexivity].
      * exact Hpre.
    + apply HBoolAssign.
    + intros ps Hadm; cbn [psatisfies]; tauto.
  - eapply HSeq with
      (eta2 := p_concentrated_mass (ntm_regions 0) (PVar ntm_y)).
    + apply HBoolAssign.
    + exact Hloop.
Qed.

(** * The headline triples

    One certificate, one loop equation [s = (Fc - Fa) * s + p]; only [q]
    and the exit mass [p] differ between the two sides. *)

Theorem ntm_left_probability :
  forall mu bb a c Fa Fc : R,
    (0 < bb)%R -> (a <= c)%R ->
    pformula_valid (ntm_cdf mu bb a Fa) ->
    pformula_valid (ntm_cdf mu bb c Fc) ->
    {{ Pr[true] = ntm_y }}
      $(ntm_prog mu bb a c)
    {{ E[$(ntm_reported_left)] = $(Fa / (Fa + (1 - Fc))) * ntm_y }}.
Proof.
  intros mu bb a c Fa Fc Hb Hac Ha Hc.
  destruct (ntm_F_range mu bb a c Fa Fc Hb Ha Hc) as [HFa HFc].
  rewrite <- ntm_reported_left_eq.
  apply ntm_prefix.
  apply (ntm_loop_derivable mu bb a c Fa (1 - Fc) Fa); try lra.
  apply ntm_body_left; assumption.
Qed.

Theorem ntm_right_probability :
  forall mu bb a c Fa Fc : R,
    (0 < bb)%R -> (a <= c)%R ->
    pformula_valid (ntm_cdf mu bb a Fa) ->
    pformula_valid (ntm_cdf mu bb c Fc) ->
    {{ Pr[true] = ntm_y }}
      $(ntm_prog mu bb a c)
    {{ E[$(ntm_reported_right)] = $((1 - Fc) / (Fa + (1 - Fc))) * ntm_y }}.
Proof.
  intros mu bb a c Fa Fc Hb Hac Ha Hc.
  destruct (ntm_F_range mu bb a c Fa Fc Hb Ha Hc) as [HFa HFc].
  rewrite <- ntm_reported_right_eq.
  apply ntm_prefix.
  apply (ntm_loop_derivable mu bb a c Fa (1 - Fc) (1 - Fc)); try lra.
  apply ntm_body_right; assumption.
Qed.

(** The two reported probabilities sum to 1: the monitor terminates almost
    surely and reports exactly one side. *)
Corollary ntm_exhaustive :
  forall mu bb a c Fa Fc : R,
    (0 < bb)%R ->
    pformula_valid (ntm_cdf mu bb a Fa) ->
    pformula_valid (ntm_cdf mu bb c Fc) ->
    (Fa / (Fa + (1 - Fc)) + (1 - Fc) / (Fa + (1 - Fc)))%R = 1%R.
Proof.
  intros mu bb a c Fa Fc Hb Ha Hc.
  destruct (ntm_F_range mu bb a c Fa Fc Hb Ha Hc) as [HFa HFc].
  field; lra.
Qed.
