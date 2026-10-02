(**
  NoisyThresholdMonitor.v -- repeated noisy thresholding.

      active := tt;
      left   := ff;
      while active do
        x      <- sample(Laplace(mu, b));
        left   := (x < a);
        active := (a <= x  /\  x < c)
      end

  THE TRIPLES ([ntm_left_probability] and [ntm_right_probability], for
  [0 < b] and [a <= c], writing [F] for the Laplace CDF at [(mu, b)]):

      { E[1_tt] = y }
          ntm_prog mu b a c
      { Pr[left  /\ ~active]  =  F a / (F a + 1 - F c) * y }

      { E[1_tt] = y }
          ntm_prog mu b a c
      { Pr[~left /\ ~active]  =  (1 - F c) / (F a + 1 - F c) * y }

  A monitor that redraws until the noisy reading leaves the band [a, c),
  then reports WHICH side it left by.  Codex's presentation nests two
  conditionals in the body; they are unnecessary.  Assigning the two
  booleans directly gives the same program and keeps the body clear of
  [HIfEq]'s shape restriction altogether.

  WHAT IS NEW HERE.  Two distinct exit events, so the postcondition's [q]
  actually selects between them: the two triples above come from ONE
  certificate, differing only in [q] and the exit mass.  Their constants
  sum to 1 ([ntm_exhaustive]), so the monitor terminates almost surely and
  reports exactly one side.  The loop equation is the same in both cases,

      s = (F c - F a) * s + r,

  differing only in the exit mass [r] -- [F a] on the left, [1 - F c] on the
  right.  That is precisely the role [q] plays in [HWhile].
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Stdlib Require Import ClassicalDescription.
From Stdlib Require Import Classical.
Require Import CPHL.
Require Import SampleBeforeLoop.
Require Import HalfLaplaceRejection.

Open Scope R_scope.
Open Scope string_scope.
Local Open Scope cphl_scope.
Local Open Scope cphl_hoare_scope.

(** * Local helpers *)

Lemma ntm_real_integral_minus :
  forall f g : R -> R,
    real_integral (fun x => (f x - g x)%R) =
    (real_integral f - real_integral g)%R.
Proof.
  intros f g.
  transitivity (real_integral (fun x => (f x + (-1) * g x)%R)).
  - apply real_integral_extensional; intro x; ring.
  - rewrite real_integral_add, real_integral_scale; ring.
Qed.

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

Definition ntm_F (mu bb u : R) : R := laplace_cdf mu bb u.

(** * Satisfaction of the atomic formulas, after a sample

    Building these first, and composing them, avoids having to steer
    [rewrite] underneath [c_not]'s implication encoding. *)

Lemma ntm_sat_below :
  forall (u z : R) (v : state),
    satisfies (update_real v ntm_x z) (ntm_below u) <-> (z < u)%R.
Proof.
  intros u z v.
  unfold ntm_below, c_lt, c_not, update_real, update_real_values.
  cbn [satisfies term_eval real_program_values].
  rewrite rpv_eq_dec_refl.
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
  unfold ntm_above, update_real, update_real_values.
  cbn [satisfies term_eval real_program_values].
  rewrite rpv_eq_dec_refl.
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

(** * Pointwise indicator identities

    Three events, all differences or complements of half-lines:
      - still inside the band        [a <= z < c]
      - exited on the left           [z < a]
      - exited on the right          [c <= z] *)

Lemma ntm_indicator_inside :
  forall (a c z : R) (v : state),
    (a <= c)%R ->
    real_indicator (satisfies (update_real v ntm_x z) (ntm_inside a c)) =
    (real_indicator (z < c)%R - real_indicator (z < a)%R)%R.
Proof.
  intros a c z v Hac.
  rewrite (real_indicator_extensional _ _ (ntm_sat_inside a c z v)).
  destruct (Rlt_dec z a) as [Hz | Hz].
  - rewrite (real_indicator_false _) by (intros [H1 H2]; lra).
    rewrite (real_indicator_true (z < c)%R) by lra.
    rewrite (real_indicator_true (z < a)%R Hz).
    ring.
  - destruct (Rlt_dec z c) as [Hc | Hc].
    + rewrite (real_indicator_true _ (conj (Rnot_lt_le _ _ Hz) Hc)).
      rewrite (real_indicator_true (z < c)%R Hc).
      rewrite (real_indicator_false (z < a)%R) by lra.
      ring.
    + rewrite (real_indicator_false _) by (intros [H1 H2]; lra).
      rewrite (real_indicator_false (z < c)%R) by lra.
      rewrite (real_indicator_false (z < a)%R) by lra.
      ring.
Qed.

Lemma ntm_indicator_left_exit :
  forall (a c z : R) (v : state),
    (a <= c)%R ->
    real_indicator
      (satisfies (update_real v ntm_x z)
         <{ $(ntm_below a) /\ (~ $(ntm_inside a c)) }>) =
    real_indicator (z < a)%R.
Proof.
  intros a c z v Hac.
  rewrite (real_indicator_extensional _ _ (ntm_sat_left_exit a c z v Hac)).
  reflexivity.
Qed.

Lemma ntm_indicator_right_exit :
  forall (a c z : R) (v : state),
    (a <= c)%R ->
    real_indicator
      (satisfies (update_real v ntm_x z)
         <{ (~ $(ntm_below a)) /\ (~ $(ntm_inside a c)) }>) =
    (1 - real_indicator (z < c)%R)%R.
Proof.
  intros a c z v Hac.
  rewrite (real_indicator_extensional _ _ (ntm_sat_right_exit a c z v Hac)).
  destruct (Rlt_dec z c) as [Hz | Hz].
  - rewrite (real_indicator_false (c <= z)%R) by lra.
    rewrite (real_indicator_true (z < c)%R Hz).
    ring.
  - rewrite (real_indicator_true (c <= z)%R) by lra.
    rewrite (real_indicator_false (z < c)%R) by lra.
    ring.
Qed.

(** * Bounds on the Laplace CDF

    Full support, so every cutoff has strictly positive mass on both
    sides -- which is what makes both exit events reachable. *)

Lemma ntm_exp_le_1 : forall x : R, (x <= 0)%R -> (exp x <= 1)%R.
Proof.
  intros x Hx.
  replace 1%R with (exp 0) by apply exp_0.
  apply exp_le_compat; exact Hx.
Qed.

Lemma ntm_exp_lt_1 : forall x : R, (x < 0)%R -> (exp x < 1)%R.
Proof.
  intros x Hx.
  replace 1%R with (exp 0) by apply exp_0.
  apply exp_increasing; exact Hx.
Qed.

Lemma laplace_cdf_pos :
  forall loc s u : R, (0 < s)%R -> (0 < laplace_cdf loc s u)%R.
Proof.
  intros loc s u Hs.
  unfold laplace_cdf.
  destruct (Rle_dec u loc) as [H | H].
  - pose proof (exp_pos ((u - loc) / s)); lra.
  - assert (Hlt : (exp (- (u - loc) / s) < 1)%R).
    { apply ntm_exp_lt_1.
      replace 0%R with (0 / s)%R by (field; lra).
      unfold Rdiv; apply Rmult_lt_compat_r;
        [apply Rinv_0_lt_compat; lra | lra]. }
    lra.
Qed.

Lemma laplace_cdf_lt_1 :
  forall loc s u : R, (0 < s)%R -> (laplace_cdf loc s u < 1)%R.
Proof.
  intros loc s u Hs.
  unfold laplace_cdf.
  destruct (Rle_dec u loc) as [H | H].
  - assert (Hle : (exp ((u - loc) / s) <= 1)%R).
    { apply ntm_exp_le_1.
      replace 0%R with (0 / s)%R by (field; lra).
      unfold Rdiv; apply Rmult_le_compat_r;
        [apply Rlt_le, Rinv_0_lt_compat; lra | lra]. }
    lra.
  - pose proof (exp_pos (- (u - loc) / s)); lra.
Qed.

(** * The three integrals *)

Lemma ntm_integral_inside :
  forall (mu bb a c : R) (v : state),
    (0 < bb)%R -> (a <= c)%R ->
    q_eval
      [[ integral ntm_x ~ $(ntm_noise mu bb),
         indicator[$(ntm_inside a c)] ]] v =
    (ntm_F mu bb c - ntm_F mu bb a)%R.
Proof.
  intros mu bb a c v Hb Hac.
  cbn [q_eval ntm_noise distribution_density term_eval].
  transitivity
    ((real_integral
        (fun z => ((1 / (2 * bb)) * exp (- Rabs (z - mu) / bb)) *
                  real_indicator (z < c)%R) -
      real_integral
        (fun z => ((1 / (2 * bb)) * exp (- Rabs (z - mu) / bb)) *
                  real_indicator (z < a)%R))%R).
  - rewrite <- ntm_real_integral_minus.
    apply real_integral_extensional; intro z.
    rewrite (ntm_indicator_inside a c z v Hac); ring.
  - rewrite !laplace_integral_strict_cdf by exact Hb.
    unfold ntm_F; ring.
Qed.

Lemma ntm_integral_left :
  forall (mu bb a c : R) (v : state),
    (0 < bb)%R -> (a <= c)%R ->
    q_eval
      [[ integral ntm_x ~ $(ntm_noise mu bb),
         indicator[$(ntm_below a) /\ (~ $(ntm_inside a c))] ]] v =
    ntm_F mu bb a.
Proof.
  intros mu bb a c v Hb Hac.
  cbn [q_eval ntm_noise distribution_density term_eval].
  transitivity
    (real_integral
       (fun z => ((1 / (2 * bb)) * exp (- Rabs (z - mu) / bb)) *
                 real_indicator (z < a)%R)).
  - apply real_integral_extensional; intro z.
    rewrite (ntm_indicator_left_exit a c z v Hac); reflexivity.
  - rewrite laplace_integral_strict_cdf by exact Hb.
    unfold ntm_F; reflexivity.
Qed.

Lemma ntm_integral_right :
  forall (mu bb a c : R) (v : state),
    (0 < bb)%R -> (a <= c)%R ->
    q_eval
      [[ integral ntm_x ~ $(ntm_noise mu bb),
         indicator[(~ $(ntm_below a)) /\ (~ $(ntm_inside a c))] ]] v =
    (1 - ntm_F mu bb c)%R.
Proof.
  intros mu bb a c v Hb Hac.
  cbn [q_eval ntm_noise distribution_density term_eval].
  transitivity
    ((real_integral
        (fun z => (1 / (2 * bb)) * exp (- Rabs (z - mu) / bb)) -
      real_integral
        (fun z => ((1 / (2 * bb)) * exp (- Rabs (z - mu) / bb)) *
                  real_indicator (z < c)%R))%R).
  - rewrite <- ntm_real_integral_minus.
    apply real_integral_extensional; intro z.
    rewrite (ntm_indicator_right_exit a c z v Hac); ring.
  - rewrite laplace_density_total by exact Hb.
    rewrite laplace_integral_strict_cdf by exact Hb.
    unfold ntm_F; reflexivity.
Qed.

(** * Certificate data *)

Definition ntm_regions (_ : nat) : CFormula := ntm_guard.

Definition ntm_transitions (mu bb a c : R) (_ _ : nat) : R :=
  (ntm_F mu bb c - ntm_F mu bb a)%R.

Definition ntm_denom (mu bb a c : R) : R :=
  (ntm_F mu bb a + (1 - ntm_F mu bb c))%R.

Definition ntm_exit_left (mu bb a : R) (_ : nat) : R := ntm_F mu bb a.

Definition ntm_exit_right (mu bb c : R) (_ : nat) : R :=
  (1 - ntm_F mu bb c)%R.

Definition ntm_sol_left (mu bb a c : R) (_ : nat) : R :=
  (ntm_F mu bb a / ntm_denom mu bb a c)%R.

Definition ntm_sol_right (mu bb a c : R) (_ : nat) : R :=
  ((1 - ntm_F mu bb c) / ntm_denom mu bb a c)%R.

Definition ntm_q_left : PConstruct := [[ indicator[ntm_left] ]].
Definition ntm_q_right : PConstruct := [[ indicator[~ ntm_left] ]].

(** Boolean substitution is the identity on the arithmetic formulas. *)
Lemma ntm_subst_inside :
  forall (b : BoolProgramVar) (beta : CFormula) (a c : R),
    subst_bool_cformula b beta (ntm_inside a c) = ntm_inside a c.
Proof. reflexivity. Qed.

Lemma ntm_subst_below :
  forall (b : BoolProgramVar) (beta : CFormula) (u : R),
    subst_bool_cformula b beta (ntm_below u) = ntm_below u.
Proof. reflexivity. Qed.

(** * The body premise, once per exit event *)

Lemma ntm_body_left :
  forall mu bb a c : R,
    (0 < bb)%R -> (a <= c)%R ->
    forall i : nat,
      (i < 1)%nat ->
      {{ $(p_concentrated_mass (ntm_regions i) (PConst 1)) }}
        $(ntm_body mu bb a c)
      {{ $(while_body_post 1 ntm_regions (ntm_transitions mu bb a c i)
             ntm_guard ntm_q_left (ntm_exit_left mu bb a i)) }}.
Proof.
  intros mu bb a c Hb Hac i Hi.
  unfold ntm_body.
  eapply HSeq with
    (eta2 :=
       subst_bool_pformula ntm_left (ntm_below a)
         (subst_bool_pformula ntm_active (ntm_inside a c)
            (while_body_post 1 ntm_regions (ntm_transitions mu bb a c i)
               ntm_guard ntm_q_left (ntm_exit_left mu bb a i)))).
  - apply HRealSample.
    + intro ps.
    + intro Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_and in Hpre.
      destruct Hpre as [_ Hmass].
      apply psatisfies_p_eq in Hmass.
      cbn [pterm_eval] in Hmass.
      unfold while_body_post, ntm_q_left, ntm_regions, ntm_guard,
        ntm_transitions, ntm_exit_left.
      cbn [finite_p_and condition_pconstruct condition_pconstruct_fuel
           pconstruct_size].
      rewrite !subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      rewrite !sample_pformula_p_and, !sample_pformula_p_eq.
      apply psatisfies_p_and; split; [apply psatisfies_p_and; split | ].
      * apply psatisfies_p_true.
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula].
        rewrite !bpv_eq_dec_refl; try rewrite !ntm_subst_inside.
        cbn [sample_pterm pterm_eval].
        rewrite (t3_expect_const ps _
                   (ntm_F mu bb c - ntm_F mu bb a)%R Hmass);
          [reflexivity | intro v; apply ntm_integral_inside; assumption].
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
             c_and c_not].
        rewrite !bpv_eq_dec_refl;
        try rewrite !ntm_subst_inside;
        try rewrite !ntm_subst_below.
        cbn [sample_pterm pterm_eval].
        rewrite (t3_expect_const ps _ (ntm_F mu bb a) Hmass);
          [reflexivity | intro v; apply ntm_integral_left; assumption].
    + intros ps _.
      revert ps.
      apply p_almost_sure_of_pointwise.
      intro v.
      unfold ntm_noise.
      cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
      intro Hle; lra.
  - eapply HSeq with
      (eta2 :=
         subst_bool_pformula ntm_active (ntm_inside a c)
           (while_body_post 1 ntm_regions (ntm_transitions mu bb a c i)
              ntm_guard ntm_q_left (ntm_exit_left mu bb a i)));
      apply HBoolAssign.
Qed.

Lemma ntm_body_right :
  forall mu bb a c : R,
    (0 < bb)%R -> (a <= c)%R ->
    forall i : nat,
      (i < 1)%nat ->
      {{ $(p_concentrated_mass (ntm_regions i) (PConst 1)) }}
        $(ntm_body mu bb a c)
      {{ $(while_body_post 1 ntm_regions (ntm_transitions mu bb a c i)
             ntm_guard ntm_q_right (ntm_exit_right mu bb c i)) }}.
Proof.
  intros mu bb a c Hb Hac i Hi.
  unfold ntm_body.
  eapply HSeq with
    (eta2 :=
       subst_bool_pformula ntm_left (ntm_below a)
         (subst_bool_pformula ntm_active (ntm_inside a c)
            (while_body_post 1 ntm_regions (ntm_transitions mu bb a c i)
               ntm_guard ntm_q_right (ntm_exit_right mu bb c i)))).
  - apply HRealSample.
    + intro ps.
    + intro Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_and in Hpre.
      destruct Hpre as [_ Hmass].
      apply psatisfies_p_eq in Hmass.
      cbn [pterm_eval] in Hmass.
      unfold while_body_post, ntm_q_right, ntm_regions, ntm_guard,
        ntm_transitions, ntm_exit_right.
      cbn [finite_p_and condition_pconstruct condition_pconstruct_fuel
           pconstruct_size].
      rewrite !subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      rewrite !sample_pformula_p_and, !sample_pformula_p_eq.
      apply psatisfies_p_and; split; [apply psatisfies_p_and; split | ].
      * apply psatisfies_p_true.
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula].
        rewrite !bpv_eq_dec_refl; try rewrite !ntm_subst_inside.
        cbn [sample_pterm pterm_eval].
        rewrite (t3_expect_const ps _
                   (ntm_F mu bb c - ntm_F mu bb a)%R Hmass);
          [reflexivity | intro v; apply ntm_integral_inside; assumption].
      * apply psatisfies_p_eq.
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
             c_and c_not].
        rewrite !bpv_eq_dec_refl;
        try rewrite !ntm_subst_inside;
        try rewrite !ntm_subst_below.
        cbn [sample_pterm pterm_eval].
        rewrite (t3_expect_const ps _ (1 - ntm_F mu bb c)%R Hmass);
          [reflexivity | intro v; apply ntm_integral_right; assumption].
    + intros ps _.
      revert ps.
      apply p_almost_sure_of_pointwise.
      intro v.
      unfold ntm_noise.
      cbn [distribution_valid_formula c_lt c_not satisfies term_eval].
      intro Hle; lra.
  - eapply HSeq with
      (eta2 :=
         subst_bool_pformula ntm_active (ntm_inside a c)
           (while_body_post 1 ntm_regions (ntm_transitions mu bb a c i)
              ntm_guard ntm_q_right (ntm_exit_right mu bb c i)));
      apply HBoolAssign.
Qed.

(** * The loops *)

Lemma ntm_loop_left :
  forall mu bb a c : R,
    (0 < bb)%R -> (a <= c)%R ->
    {{ $(p_concentrated_mass (ntm_regions 0) (PVar ntm_y)) }}
      $(ntm_loop mu bb a c)
    {{ E[$(condition_pconstruct ntm_q_left (c_not ntm_guard))]
         = $(ntm_sol_left mu bb a c 0) * ntm_y }}.
Proof.
  intros mu bb a c Hb Hac.
  pose proof (laplace_cdf_pos mu bb a Hb) as HFa.
  pose proof (laplace_cdf_lt_1 mu bb c Hb) as HFc.
  assert (HD : (0 < ntm_denom mu bb a c)%R).
  { unfold ntm_denom, ntm_F; lra. }
  eapply HWhile with
    (m := 1%nat) (k := 0%nat)
    (regions := ntm_regions) (solution := ntm_sol_left mu bb a c)
    (exits := ntm_exit_left mu bb a)
    (transitions := ntm_transitions mu bb a c).
  - lia.
  - unfold while_regions_cover, cformula_valid, ntm_regions.
    intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
  - unfold while_regions_in_guard, cformula_valid, ntm_regions.
    intros i Hi v; cbn [satisfies]; tauto.
  - unfold while_regions_disjoint; intros i j Hi Hj; lia.
  - unfold while_progress, ntm_exit_left, ntm_F.
    intros i Hi; left; lra.
  - apply ntm_body_left; assumption.
  - unfold while_solution, ntm_sol_left, ntm_transitions, ntm_exit_left,
      ntm_denom, ntm_F.
    intros i Hi.
    cbn [finite_r_sum].
    unfold ntm_denom, ntm_F in HD.
    assert (Hval :
      (laplace_cdf mu bb a /
       (laplace_cdf mu bb a + (1 - laplace_cdf mu bb c)) *
       (laplace_cdf mu bb a + (1 - laplace_cdf mu bb c)))%R =
      laplace_cdf mu bb a) by (field; lra).
    split.
    + field; lra.
    + split.
      * apply Rmult_le_reg_r
          with (r := (laplace_cdf mu bb a + (1 - laplace_cdf mu bb c))%R);
          [lra |].
        rewrite Hval; lra.
      * apply Rmult_le_reg_r
          with (r := (laplace_cdf mu bb a + (1 - laplace_cdf mu bb c))%R);
          [lra |].
        rewrite Hval; lra.
Qed.

Lemma ntm_loop_right :
  forall mu bb a c : R,
    (0 < bb)%R -> (a <= c)%R ->
    {{ $(p_concentrated_mass (ntm_regions 0) (PVar ntm_y)) }}
      $(ntm_loop mu bb a c)
    {{ E[$(condition_pconstruct ntm_q_right (c_not ntm_guard))]
         = $(ntm_sol_right mu bb a c 0) * ntm_y }}.
Proof.
  intros mu bb a c Hb Hac.
  pose proof (laplace_cdf_pos mu bb a Hb) as HFa.
  pose proof (laplace_cdf_lt_1 mu bb c Hb) as HFc.
  eapply HWhile with
    (m := 1%nat) (k := 0%nat)
    (regions := ntm_regions) (solution := ntm_sol_right mu bb a c)
    (exits := ntm_exit_right mu bb c)
    (transitions := ntm_transitions mu bb a c).
  - lia.
  - unfold while_regions_cover, cformula_valid, ntm_regions.
    intro v; cbn [finite_c_or c_or c_not satisfies]; tauto.
  - unfold while_regions_in_guard, cformula_valid, ntm_regions.
    intros i Hi v; cbn [satisfies]; tauto.
  - unfold while_regions_disjoint; intros i j Hi Hj; lia.
  - unfold while_progress, ntm_exit_right, ntm_F.
    intros i Hi; left; lra.
  - apply ntm_body_right; assumption.
  - unfold while_solution, ntm_sol_right, ntm_transitions, ntm_exit_right,
      ntm_denom, ntm_F.
    intros i Hi.
    cbn [finite_r_sum].
    assert (Hval :
      ((1 - laplace_cdf mu bb c) /
       (laplace_cdf mu bb a + (1 - laplace_cdf mu bb c)) *
       (laplace_cdf mu bb a + (1 - laplace_cdf mu bb c)))%R =
      (1 - laplace_cdf mu bb c)%R) by (field; lra).
    split.
    + field; lra.
    + split.
      * apply Rmult_le_reg_r
          with (r := (laplace_cdf mu bb a + (1 - laplace_cdf mu bb c))%R);
          [lra |].
        rewrite Hval; lra.
      * apply Rmult_le_reg_r
          with (r := (laplace_cdf mu bb a + (1 - laplace_cdf mu bb c))%R);
          [lra |].
        rewrite Hval; lra.
Qed.

(** * The monitor

    The prefix concentrates all mass on the single region, so the loop is
    enterable. *)

Lemma ntm_prefix :
  forall (mu bb a c : R) (theta : PFormula),
    {{ $(p_concentrated_mass (ntm_regions 0) (PVar ntm_y)) }}
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
    + intro ps.
    + intro Hadm.
      cbn [psatisfies].
      intro Hpre.
      apply psatisfies_p_eq in Hpre.
      cbn [pterm_eval] in Hpre.
      unfold p_concentrated_mass, ntm_regions, ntm_guard.
      rewrite !subst_bool_pformula_p_and, !subst_bool_pformula_p_eq.
      apply psatisfies_p_and; split; apply psatisfies_p_eq;
        cbn [subst_bool_pterm subst_bool_pconstruct subst_bool_cformula
             pterm_eval].
      * rewrite !bpv_eq_dec_refl; reflexivity.
      * exact Hpre.
    + apply HBoolAssign.
    + intro ps; cbn [psatisfies]; tauto.
  - eapply HSeq with
      (eta2 := p_concentrated_mass (ntm_regions 0) (PVar ntm_y)).
    + apply HBoolAssign.
    + exact Hloop.
Qed.

(** The monitor reports LEFT with probability [F a / (F a + 1 - F c)]. *)
Theorem ntm_left_probability :
  forall mu bb a c : R,
    (0 < bb)%R -> (a <= c)%R ->
    {{ Pr[true] = ntm_y }}
      $(ntm_prog mu bb a c)
    {{ E[$(condition_pconstruct ntm_q_left (c_not ntm_guard))]
         = $(ntm_F mu bb a /
             (ntm_F mu bb a + (1 - ntm_F mu bb c))) * ntm_y }}.
Proof.
  intros mu bb a c Hb Hac.
  apply ntm_prefix.
  apply ntm_loop_left; assumption.
Qed.

(** ... and RIGHT with probability [(1 - F c) / (F a + 1 - F c)].  Same
    certificate, same loop equation -- only [q] and the exit mass differ. *)
Theorem ntm_right_probability :
  forall mu bb a c : R,
    (0 < bb)%R -> (a <= c)%R ->
    {{ Pr[true] = ntm_y }}
      $(ntm_prog mu bb a c)
    {{ E[$(condition_pconstruct ntm_q_right (c_not ntm_guard))]
         = $((1 - ntm_F mu bb c) /
             (ntm_F mu bb a + (1 - ntm_F mu bb c))) * ntm_y }}.
Proof.
  intros mu bb a c Hb Hac.
  apply ntm_prefix.
  apply ntm_loop_right; assumption.
Qed.

(** The two reported probabilities sum to 1: the monitor terminates almost
    surely and reports exactly one side. *)
Corollary ntm_exhaustive :
  forall mu bb a c : R,
    (0 < bb)%R ->
    (ntm_F mu bb a / (ntm_F mu bb a + (1 - ntm_F mu bb c)) +
     (1 - ntm_F mu bb c) / (ntm_F mu bb a + (1 - ntm_F mu bb c)))%R = 1%R.
Proof.
  intros mu bb a c Hb.
  pose proof (laplace_cdf_pos mu bb a Hb) as HFa.
  pose proof (laplace_cdf_lt_1 mu bb c Hb) as HFc.
  unfold ntm_F in *.
  field; lra.
Qed.
